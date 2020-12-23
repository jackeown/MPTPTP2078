%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t147_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) != k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) != k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t147_zfmisc_1.p',t147_zfmisc_1)).

fof(f41,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t147_zfmisc_1.p',t17_zfmisc_1)).

fof(f40,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t147_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f39,plain,
    ( k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t147_zfmisc_1.p',t87_xboole_1)).

fof(f38,plain,(
    k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) != k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) != k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
