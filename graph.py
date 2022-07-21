import sys
import matplotlib.pyplot as plt
import ast
import pandas as pd
from sklearn import linear_model
from sklearn import datasets
from sklearn.datasets import make_moons
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import scale
from scipy.special import expit
import numpy as np
from functools import reduce
from itertools import groupby
from scipy.stats import gaussian_kde
from scipy.interpolate import make_interp_spline

# Remove consecutive duplicates
def removeDuplicates(xs):
  return [v for i, v in enumerate(xs) if i == 0 or v != xs[i-1]]

def main():
  arg  = sys.argv[1]
  f    = open("model-output.txt", "r")

  data = ast.literal_eval(f.read().replace('-Infinity', '-2e308')) #

  if arg in ["simLinRegr", "simLinRegrMB"]:
    xs = [xy[0] for xy in data]
    ys = [xy[1] for xy in data]
    plt.scatter(xs, ys)
    plt.xlabel('x data points')
    plt.ylabel('y data points')
    plt.show()
  if arg in ["mhLinRegrMB", "smcLinRegrMB", "rmsmcLinRegrMB"]: # Remove duplicates from mh trace
    if arg in ["mhLinRegrMB"]:
      mus = removeDuplicates(data[0])
      cs  = removeDuplicates(data[1])
    elif arg in ["smcLinRegrMB", "rmsmcLinRegrMB"]:
      mus = data[0]
      cs  = data[1]
    _, axs1 = plt.subplots(nrows=1)
    axs1.set_xlabel("mu values", fontsize=12)
    axs1.set_ylabel("frequency")
    axs1.hist(mus,bins=25)
    _, axs2 = plt.subplots(nrows=1)
    axs2.set_xlabel("c values", fontsize=12)
    axs2.set_ylabel("frequency")
    axs2.hist(cs, bins=25)
    plt.show()

  if arg in ["simHMM", "simHMMMB"]:
    xs = [xy[0] for xy in data]
    ys = [xy[1] for xy in data]
    plt.scatter(xs, ys)
    plt.xlabel('x data points')
    plt.ylabel('y data points')
    plt.show()
  if arg in ["mhHMMMB", "smcHMMMB", "rmsmcHMMMB"]: # Remove duplicates from mh trace
    if arg in ["mhHMMMB"]:
      trans_ps = removeDuplicates(data[0])
      obs_ps   = removeDuplicates(data[1])
    elif arg in ["smcHMMMB", "rmsmcHMMMB"]:
      trans_ps = data[0]
      obs_ps  = data[1]
    fig1, axs1 = plt.subplots(nrows=1)
    axs1.set_xlabel("trans_p values", fontsize=12)
    axs1.set_ylabel("frequency")
    axs1.hist(trans_ps,bins=25)
    fig2, axs2 = plt.subplots(nrows=1)
    axs2.set_xlabel("obs_p values", fontsize=12)
    axs2.set_ylabel("frequency")
    axs2.hist(obs_ps, bins=25)
    plt.show()

  if arg in ["mhLDAMB", "rmsmcLDAMB"]:
    ws       = ['DNA', 'evolution', 'parsing', 'phonology']
    topic_ps = data[0]
    # Average the trace or final population of parameter values for topics
    topic_ps_avg = sum(np.array(topic_ps))/(len(topic_ps))
    print(topic_ps)
    topic_word_ps = data[1]
    # Average the trace or final population of parameter values for words
    topic_word_ps_avg = sum(np.array(topic_word_ps))/(len(topic_word_ps))
    topic_0s_avg = topic_word_ps_avg[0]
    topic_1s_avg = topic_word_ps_avg[1]
    print(topic_word_ps)
    fig, ax = plt.subplots(nrows=1)
    ax.bar(['Topic 0', 'Topic 1'], topic_ps_avg, 0.8)
    ax.set_xticklabels(['Topic 0', 'Topic 1'])
    plt.title('Document-Topic Distribution')
    fig0, ax0 = plt.subplots(nrows=1)
    ax0.bar(ws, topic_0s_avg, 0.8)
    ax0.set_xticklabels(ws)
    plt.title('Topic-Word Distribution 0')
    fig1, ax1 = plt.subplots(nrows=1)
    ax1.bar(ws, topic_1s_avg, 0.8)
    ax1.set_xticklabels(ws)
    plt.title('Topic-Word Distribution 1')
    plt.show()

  if arg in ["simSIR", "simSIRMB" "simSIRSMB"]:
    # y axis
    sir_values   = np.array(data[0])
    obs_infected = np.array(data[1])
    sus            = np.array([sir[0] for sir in sir_values])
    inf            = np.array([sir[1][0] for sir in sir_values])
    recov          = np.array([sir[1][1] for sir in sir_values])
    # x axis
    timeSteps      = np.array([ t for t in range(len(sus))])
    # interpolate data
    X_ = np.linspace(timeSteps.min(), timeSteps.max(), 300)
    X_S_Spline = make_interp_spline(timeSteps.ravel(), sus.ravel())
    X_I_Spline = make_interp_spline(timeSteps.ravel(), inf.ravel())
    X_R_Spline = make_interp_spline(timeSteps.ravel(), recov.ravel())
    X_InfCount_Spline = make_interp_spline(timeSteps.ravel(), obs_infected.ravel())
    S_ = X_S_Spline(X_)
    I_ = X_I_Spline(X_)
    R_ = X_R_Spline(X_)
    IC_ = X_InfCount_Spline(X_)

    fig1, axs1 = plt.subplots(nrows=1)
    axs1.set_xlabel("days")
    axs1.set_ylabel("population", fontsize=12)
    axs1.plot(X_, S_, color='blue', label='Actual Susceptible')
    axs1.plot(X_, I_, color='red', label='Actual Infected')
    axs1.plot(X_, R_, color='green', label='Actual Recovered')
    axs1.plot(X_, IC_, color='black', label='Reported Infected')
    axs1.set_title('SIR model - Simulation')
    plt.xlim([0,100])
    plt.ylim([0,800])
    plt.legend()
    plt.show()
  if arg == "mhSIRMB":
    print(data)
    betas_unique   = data[0]
    gammas_unique  = data[1][0]
    rhos_unique    = data[1][1]
    _, axs1 = plt.subplots(nrows=1)
    axs1.set_xlabel("β values", fontsize=12)
    axs1.set_ylabel("frequency")
    axs1.hist(betas_unique, bins=25)
    axs1.set_title('SIR - Metropolis Hastings Posterior (Beta)')
    _, axs2 = plt.subplots(nrows=1)
    axs2.set_xlabel("γ values", fontsize=12)
    axs2.set_ylabel("frequency")
    axs2.hist(gammas_unique, bins=25)
    axs2.set_title('HMM - Metropolis Hastings Posterior (Gamma)')
    _, axs3 = plt.subplots(nrows=1)
    axs3.set_xlabel("ρ values", fontsize=12)
    axs3.set_ylabel("frequency")
    axs3.hist(rhos_unique, bins=25)
    axs3.set_title('HMM - Metropolis Hastings Posterior (Rho)')
    plt.show()
if __name__ == "__main__":
  main()