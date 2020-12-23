%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0302+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 196 expanded)
%              Number of leaves         :    7 (  48 expanded)
%              Depth                    :   22
%              Number of atoms          :  150 ( 772 expanded)
%              Number of equality atoms :   53 ( 354 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f97,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f93,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f93,plain,(
    ! [X8] : ~ r2_hidden(X8,sK0) ),
    inference(subsumption_resolution,[],[f89,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f84,f23])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK1),sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(condensation,[],[f72])).

fof(f72,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(sK3(sK0,sK1),sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f28,f19])).

fof(f19,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,sK1)),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,sK1)),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X2,sK0)
      | sK0 = sK1 ) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(X5,sK3(sK0,sK1)),k2_zfmisc_1(X6,sK1))
      | ~ r2_hidden(X7,sK0)
      | sK0 = sK1
      | ~ r2_hidden(k4_tarski(X8,sK3(sK0,sK1)),k2_zfmisc_1(X9,sK1)) ) ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,X4),X3)
      | X3 = X4
      | ~ r2_hidden(k4_tarski(X5,sK3(X3,X4)),k2_zfmisc_1(X6,X4)) ) ),
    inference(resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK0,sK1),sK0)
      | ~ r2_hidden(k4_tarski(X1,sK3(sK0,sK1)),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sK0 = sK1
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X1,sK3(sK0,sK1)),k2_zfmisc_1(X2,sK1))
      | r2_hidden(sK3(sK0,sK1),sK0) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sK0 = sK1
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X1,sK3(sK0,sK1)),k2_zfmisc_1(X2,sK1))
      | r2_hidden(sK3(sK0,sK1),sK0)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(sK3(sK0,X7),sK1)
      | sK0 = X7
      | ~ r2_hidden(X9,sK0)
      | ~ r2_hidden(k4_tarski(X6,sK3(sK0,X7)),k2_zfmisc_1(X8,X7)) ) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( ~ r2_hidden(k4_tarski(sK3(X13,X14),X17),k2_zfmisc_1(X13,X18))
      | ~ r2_hidden(k4_tarski(X15,sK3(X13,X14)),k2_zfmisc_1(X16,X14))
      | X13 = X14 ) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK3(sK0,sK1),sK0)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f76,f24])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK1),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(condensation,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK3(sK0,sK1),sK1)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f69,f28])).

%------------------------------------------------------------------------------
