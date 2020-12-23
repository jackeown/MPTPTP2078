%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0880+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:49 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  20 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f21,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f21,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK3)) ),
    inference(superposition,[],[f14,f13])).

fof(f14,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f9,f10,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f9,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).

%------------------------------------------------------------------------------
