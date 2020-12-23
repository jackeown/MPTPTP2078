%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:57 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  190 (7567 expanded)
%              Number of leaves         :   29 (2297 expanded)
%              Depth                    :   33
%              Number of atoms          :  286 (14555 expanded)
%              Number of equality atoms :  159 (6601 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1415,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1412,f102])).

fof(f102,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f97,f99])).

fof(f99,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f97,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f1412,plain,(
    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1300,f1107])).

fof(f1107,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(backward_demodulation,[],[f1070,f1085])).

fof(f1085,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f1045,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1045,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f53,f859])).

fof(f859,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f853,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f853,plain,(
    ! [X9] : r1_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f852,f816])).

fof(f816,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = X1 ),
    inference(forward_demodulation,[],[f815,f90])).

fof(f90,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f60,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f815,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f814,f147])).

fof(f147,plain,(
    k1_xboole_0 = k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f142,f125])).

fof(f125,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f46,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f142,plain,(
    k1_xboole_0 = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) ),
    inference(superposition,[],[f89,f123])).

fof(f123,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f111,f65])).

fof(f111,plain,(
    r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f53,f106])).

fof(f106,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f104,f65])).

fof(f104,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f103,f96])).

fof(f96,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f103,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f100,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f46,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f50,f87])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f814,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1))) ),
    inference(forward_demodulation,[],[f744,f123])).

fof(f744,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f677,f712])).

fof(f712,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f711,f525])).

fof(f525,plain,(
    sK1 = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f404,f524])).

fof(f524,plain,(
    sK1 = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f523,f90])).

fof(f523,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f522,f393])).

fof(f393,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f172,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f172,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f170,f65])).

fof(f170,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f140,f96])).

fof(f140,plain,(
    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f108,f61])).

fof(f108,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f107,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f66,f99])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f522,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f509,f55])).

fof(f509,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k3_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(superposition,[],[f131,f89])).

fof(f131,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1)) ),
    inference(backward_demodulation,[],[f122,f130])).

fof(f130,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f128,f109])).

fof(f109,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f106,f55])).

fof(f128,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f88,f109])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f87])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f122,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),X1)) ),
    inference(forward_demodulation,[],[f118,f120])).

fof(f120,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f116,f109])).

fof(f116,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1) ),
    inference(superposition,[],[f91,f106])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f87,f87])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f118,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),X1)) ),
    inference(superposition,[],[f93,f106])).

fof(f93,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f74,f87,f87,f87,f87])).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f404,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f400,f393])).

fof(f400,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f91,f172])).

fof(f711,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f707,f393])).

fof(f707,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f88,f393])).

fof(f677,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))) ),
    inference(superposition,[],[f225,f91])).

fof(f225,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X1)) ),
    inference(forward_demodulation,[],[f221,f55])).

fof(f221,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),X1)) ),
    inference(superposition,[],[f93,f167])).

fof(f167,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) = k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)) ),
    inference(forward_demodulation,[],[f165,f137])).

fof(f137,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f108,f67])).

fof(f165,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),sK1) = k3_tarski(k6_enumset1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),sK1)) ),
    inference(resolution,[],[f124,f108])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k3_tarski(k6_enumset1(k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),sK1)) ) ),
    inference(resolution,[],[f98,f66])).

fof(f852,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f851,f147])).

fof(f851,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),X9)) ),
    inference(forward_demodulation,[],[f752,f123])).

fof(f752,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),X9)) ),
    inference(backward_demodulation,[],[f694,f712])).

fof(f694,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X9)) ),
    inference(superposition,[],[f52,f225])).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1070,plain,(
    ! [X6] : k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = X6 ),
    inference(forward_demodulation,[],[f1047,f90])).

fof(f1047,plain,(
    ! [X6] : k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k1_xboole_0)),k3_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f88,f859])).

fof(f1300,plain,(
    sK0 = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f915,f1296])).

fof(f1296,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1264,f68])).

fof(f1264,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f52,f712])).

fof(f915,plain,(
    sK0 = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f914,f90])).

fof(f914,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f913,f207])).

fof(f207,plain,(
    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f206,f55])).

fof(f206,plain,(
    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f203,f197])).

fof(f197,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,k4_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f108,f94])).

fof(f203,plain,(
    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f91,f135])).

fof(f135,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f108,f98])).

fof(f913,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f912,f135])).

fof(f912,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f886,f55])).

fof(f886,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[],[f780,f90])).

fof(f780,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) ),
    inference(backward_demodulation,[],[f208,f779])).

fof(f779,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)) ),
    inference(backward_demodulation,[],[f336,f778])).

fof(f778,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) ),
    inference(forward_demodulation,[],[f777,f656])).

fof(f656,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) ),
    inference(backward_demodulation,[],[f160,f655])).

fof(f655,plain,(
    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f654,f141])).

fof(f141,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(resolution,[],[f134,f68])).

fof(f134,plain,(
    r1_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f52,f119])).

fof(f119,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f115,f89])).

fof(f115,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f88,f106])).

fof(f654,plain,(
    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f646,f640])).

fof(f640,plain,(
    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f90,f569])).

fof(f569,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f265,f169])).

fof(f169,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f168,f68])).

fof(f168,plain,(
    r1_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f52,f148])).

fof(f148,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f145,f89])).

fof(f145,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f88,f123])).

fof(f265,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k3_xboole_0(sK0,k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f127,f55])).

fof(f127,plain,(
    ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f75,f109])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f646,plain,(
    k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f91,f569])).

fof(f160,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),X1)) ),
    inference(superposition,[],[f93,f141])).

fof(f777,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) ),
    inference(forward_demodulation,[],[f776,f147])).

fof(f776,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) ),
    inference(forward_demodulation,[],[f739,f123])).

fof(f739,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) ),
    inference(backward_demodulation,[],[f668,f712])).

fof(f668,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) ),
    inference(superposition,[],[f225,f131])).

fof(f336,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1)))) ),
    inference(superposition,[],[f93,f197])).

fof(f208,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)) ),
    inference(backward_demodulation,[],[f205,f207])).

fof(f205,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)) ),
    inference(forward_demodulation,[],[f201,f55])).

fof(f201,plain,(
    ! [X1] : k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),X1)) ),
    inference(superposition,[],[f93,f135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.47  % (5906)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.48  % (5898)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.48  % (5906)Refutation not found, incomplete strategy% (5906)------------------------------
% 0.20/0.48  % (5906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5906)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (5906)Memory used [KB]: 10746
% 0.20/0.48  % (5906)Time elapsed: 0.071 s
% 0.20/0.48  % (5906)------------------------------
% 0.20/0.48  % (5906)------------------------------
% 0.20/0.49  % (5885)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (5890)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (5892)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (5907)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (5911)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (5887)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (5912)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (5889)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (5888)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (5899)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (5891)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (5894)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (5903)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (5884)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (5904)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (5901)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (5905)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (5908)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (5893)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (5886)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (5913)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (5896)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (5895)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (5897)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (5909)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (5900)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (5910)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (5901)Refutation not found, incomplete strategy% (5901)------------------------------
% 0.20/0.55  % (5901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5901)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5901)Memory used [KB]: 10618
% 0.20/0.55  % (5901)Time elapsed: 0.143 s
% 0.20/0.55  % (5901)------------------------------
% 0.20/0.55  % (5901)------------------------------
% 0.20/0.55  % (5902)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.32/0.67  % (5924)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.32/0.70  % (5925)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.75/0.71  % (5892)Refutation found. Thanks to Tanya!
% 2.75/0.71  % SZS status Theorem for theBenchmark
% 2.75/0.72  % SZS output start Proof for theBenchmark
% 2.75/0.72  fof(f1415,plain,(
% 2.75/0.72    $false),
% 2.75/0.72    inference(subsumption_resolution,[],[f1412,f102])).
% 2.75/0.72  fof(f102,plain,(
% 2.75/0.72    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(backward_demodulation,[],[f97,f99])).
% 2.75/0.72  fof(f99,plain,(
% 2.75/0.72    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.75/0.72    inference(resolution,[],[f46,f67])).
% 2.75/0.72  fof(f67,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f35])).
% 2.75/0.72  fof(f35,plain,(
% 2.75/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.72    inference(ennf_transformation,[],[f24])).
% 2.75/0.72  fof(f24,axiom,(
% 2.75/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.75/0.72  fof(f46,plain,(
% 2.75/0.72    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(cnf_transformation,[],[f40])).
% 2.75/0.72  fof(f40,plain,(
% 2.75/0.72    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f39])).
% 2.75/0.72  fof(f39,plain,(
% 2.75/0.72    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.75/0.72    introduced(choice_axiom,[])).
% 2.75/0.72  fof(f31,plain,(
% 2.75/0.72    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.72    inference(ennf_transformation,[],[f29])).
% 2.75/0.72  fof(f29,negated_conjecture,(
% 2.75/0.72    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.75/0.72    inference(negated_conjecture,[],[f28])).
% 2.75/0.72  fof(f28,conjecture,(
% 2.75/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.75/0.72  fof(f97,plain,(
% 2.75/0.72    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f47,f49])).
% 2.75/0.72  fof(f49,plain,(
% 2.75/0.72    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f23])).
% 2.75/0.72  fof(f23,axiom,(
% 2.75/0.72    ! [X0] : k2_subset_1(X0) = X0),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.75/0.72  fof(f47,plain,(
% 2.75/0.72    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.75/0.72    inference(cnf_transformation,[],[f40])).
% 2.75/0.72  fof(f1412,plain,(
% 2.75/0.72    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(superposition,[],[f1300,f1107])).
% 2.75/0.72  fof(f1107,plain,(
% 2.75/0.72    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 2.75/0.72    inference(backward_demodulation,[],[f1070,f1085])).
% 2.75/0.72  fof(f1085,plain,(
% 2.75/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.75/0.72    inference(resolution,[],[f1045,f65])).
% 2.75/0.72  fof(f65,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f33])).
% 2.75/0.72  fof(f33,plain,(
% 2.75/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.75/0.72    inference(ennf_transformation,[],[f9])).
% 2.75/0.72  fof(f9,axiom,(
% 2.75/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.75/0.72  fof(f1045,plain,(
% 2.75/0.72    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 2.75/0.72    inference(superposition,[],[f53,f859])).
% 2.75/0.72  fof(f859,plain,(
% 2.75/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 2.75/0.72    inference(resolution,[],[f853,f68])).
% 2.75/0.72  fof(f68,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f36])).
% 2.75/0.72  fof(f36,plain,(
% 2.75/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.75/0.72    inference(ennf_transformation,[],[f30])).
% 2.75/0.72  fof(f30,plain,(
% 2.75/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.75/0.72    inference(unused_predicate_definition_removal,[],[f3])).
% 2.75/0.72  fof(f3,axiom,(
% 2.75/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.75/0.72  fof(f853,plain,(
% 2.75/0.72    ( ! [X9] : (r1_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f852,f816])).
% 2.75/0.72  fof(f816,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = X1) )),
% 2.75/0.72    inference(forward_demodulation,[],[f815,f90])).
% 2.75/0.72  fof(f90,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.75/0.72    inference(definition_unfolding,[],[f51,f87])).
% 2.75/0.72  fof(f87,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f60,f86])).
% 2.75/0.72  fof(f86,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f57,f85])).
% 2.75/0.72  fof(f85,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.75/0.72    inference(definition_unfolding,[],[f58,f84])).
% 2.75/0.72  fof(f84,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.75/0.72    inference(definition_unfolding,[],[f73,f83])).
% 2.75/0.72  fof(f83,plain,(
% 2.75/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.75/0.72    inference(definition_unfolding,[],[f77,f82])).
% 2.75/0.72  fof(f82,plain,(
% 2.75/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.75/0.72    inference(definition_unfolding,[],[f78,f81])).
% 2.75/0.72  fof(f81,plain,(
% 2.75/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.75/0.72    inference(definition_unfolding,[],[f79,f80])).
% 2.75/0.72  fof(f80,plain,(
% 2.75/0.72    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f19])).
% 2.75/0.72  fof(f19,axiom,(
% 2.75/0.72    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.75/0.72  fof(f79,plain,(
% 2.75/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f18])).
% 2.75/0.72  fof(f18,axiom,(
% 2.75/0.72    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.75/0.72  fof(f78,plain,(
% 2.75/0.72    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f17])).
% 2.75/0.72  fof(f17,axiom,(
% 2.75/0.72    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.75/0.72  fof(f77,plain,(
% 2.75/0.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f16])).
% 2.75/0.72  fof(f16,axiom,(
% 2.75/0.72    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.75/0.72  fof(f73,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f15])).
% 2.75/0.72  fof(f15,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.75/0.72  fof(f58,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f14])).
% 2.75/0.72  fof(f14,axiom,(
% 2.75/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.75/0.72  fof(f57,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f21])).
% 2.75/0.72  fof(f21,axiom,(
% 2.75/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.75/0.72  fof(f60,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f4])).
% 2.75/0.72  fof(f4,axiom,(
% 2.75/0.72    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.75/0.72  fof(f51,plain,(
% 2.75/0.72    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f10])).
% 2.75/0.72  fof(f10,axiom,(
% 2.75/0.72    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.75/0.72  fof(f815,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f814,f147])).
% 2.75/0.72  fof(f147,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1)),
% 2.75/0.72    inference(forward_demodulation,[],[f142,f125])).
% 2.75/0.72  fof(f125,plain,(
% 2.75/0.72    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(sK0,sK1,sK1)),
% 2.75/0.72    inference(resolution,[],[f98,f46])).
% 2.75/0.72  fof(f98,plain,(
% 2.75/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))) )),
% 2.75/0.72    inference(resolution,[],[f46,f94])).
% 2.75/0.72  fof(f94,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f76,f86])).
% 2.75/0.72  fof(f76,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f38])).
% 2.75/0.72  fof(f38,plain,(
% 2.75/0.72    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.72    inference(flattening,[],[f37])).
% 2.75/0.72  fof(f37,plain,(
% 2.75/0.72    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.75/0.72    inference(ennf_transformation,[],[f27])).
% 2.75/0.72  fof(f27,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.75/0.72  fof(f142,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1)),
% 2.75/0.72    inference(superposition,[],[f89,f123])).
% 2.75/0.72  fof(f123,plain,(
% 2.75/0.72    sK1 = k3_xboole_0(sK1,sK1)),
% 2.75/0.72    inference(resolution,[],[f111,f65])).
% 2.75/0.72  fof(f111,plain,(
% 2.75/0.72    r1_tarski(sK1,sK1)),
% 2.75/0.72    inference(superposition,[],[f53,f106])).
% 2.75/0.72  fof(f106,plain,(
% 2.75/0.72    sK1 = k3_xboole_0(sK1,sK0)),
% 2.75/0.72    inference(resolution,[],[f104,f65])).
% 2.75/0.72  fof(f104,plain,(
% 2.75/0.72    r1_tarski(sK1,sK0)),
% 2.75/0.72    inference(resolution,[],[f103,f96])).
% 2.75/0.72  fof(f96,plain,(
% 2.75/0.72    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.75/0.72    inference(equality_resolution,[],[f69])).
% 2.75/0.72  fof(f69,plain,(
% 2.75/0.72    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.75/0.72    inference(cnf_transformation,[],[f45])).
% 2.75/0.72  fof(f45,plain,(
% 2.75/0.72    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.75/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 2.75/0.72  fof(f44,plain,(
% 2.75/0.72    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.75/0.72    introduced(choice_axiom,[])).
% 2.75/0.72  fof(f43,plain,(
% 2.75/0.72    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.75/0.72    inference(rectify,[],[f42])).
% 2.75/0.72  fof(f42,plain,(
% 2.75/0.72    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.75/0.72    inference(nnf_transformation,[],[f20])).
% 2.75/0.72  fof(f20,axiom,(
% 2.75/0.72    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.75/0.72  fof(f103,plain,(
% 2.75/0.72    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(subsumption_resolution,[],[f100,f48])).
% 2.75/0.72  fof(f48,plain,(
% 2.75/0.72    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f26])).
% 2.75/0.72  fof(f26,axiom,(
% 2.75/0.72    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.75/0.72  fof(f100,plain,(
% 2.75/0.72    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(resolution,[],[f46,f61])).
% 2.75/0.72  fof(f61,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f41])).
% 2.75/0.72  fof(f41,plain,(
% 2.75/0.72    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.75/0.72    inference(nnf_transformation,[],[f32])).
% 2.75/0.72  fof(f32,plain,(
% 2.75/0.72    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.75/0.72    inference(ennf_transformation,[],[f22])).
% 2.75/0.72  fof(f22,axiom,(
% 2.75/0.72    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.75/0.72  fof(f89,plain,(
% 2.75/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f50,f87])).
% 2.75/0.72  fof(f50,plain,(
% 2.75/0.72    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f13])).
% 2.75/0.72  fof(f13,axiom,(
% 2.75/0.72    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.75/0.72  fof(f814,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1)))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f744,f123])).
% 2.75/0.72  fof(f744,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1))))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f677,f712])).
% 2.75/0.72  fof(f712,plain,(
% 2.75/0.72    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f711,f525])).
% 2.75/0.72  fof(f525,plain,(
% 2.75/0.72    sK1 = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(backward_demodulation,[],[f404,f524])).
% 2.75/0.72  fof(f524,plain,(
% 2.75/0.72    sK1 = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f523,f90])).
% 2.75/0.72  fof(f523,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f522,f393])).
% 2.75/0.72  fof(f393,plain,(
% 2.75/0.72    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(superposition,[],[f172,f55])).
% 2.75/0.72  fof(f55,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f1])).
% 2.75/0.72  fof(f1,axiom,(
% 2.75/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.75/0.72  fof(f172,plain,(
% 2.75/0.72    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 2.75/0.72    inference(resolution,[],[f170,f65])).
% 2.75/0.72  fof(f170,plain,(
% 2.75/0.72    r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 2.75/0.72    inference(resolution,[],[f140,f96])).
% 2.75/0.72  fof(f140,plain,(
% 2.75/0.72    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(subsumption_resolution,[],[f138,f48])).
% 2.75/0.72  fof(f138,plain,(
% 2.75/0.72    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(resolution,[],[f108,f61])).
% 2.75/0.72  fof(f108,plain,(
% 2.75/0.72    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(subsumption_resolution,[],[f107,f46])).
% 2.75/0.72  fof(f107,plain,(
% 2.75/0.72    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.75/0.72    inference(superposition,[],[f66,f99])).
% 2.75/0.72  fof(f66,plain,(
% 2.75/0.72    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f34])).
% 2.75/0.72  fof(f34,plain,(
% 2.75/0.72    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.72    inference(ennf_transformation,[],[f25])).
% 2.75/0.72  fof(f25,axiom,(
% 2.75/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.75/0.72  fof(f522,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f509,f55])).
% 2.75/0.72  fof(f509,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k3_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 2.75/0.72    inference(superposition,[],[f131,f89])).
% 2.75/0.72  fof(f131,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f122,f130])).
% 2.75/0.72  fof(f130,plain,(
% 2.75/0.72    k4_xboole_0(sK0,sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)),
% 2.75/0.72    inference(forward_demodulation,[],[f128,f109])).
% 2.75/0.72  fof(f109,plain,(
% 2.75/0.72    sK1 = k3_xboole_0(sK0,sK1)),
% 2.75/0.72    inference(superposition,[],[f106,f55])).
% 2.75/0.72  fof(f128,plain,(
% 2.75/0.72    k4_xboole_0(sK0,sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(superposition,[],[f88,f109])).
% 2.75/0.72  fof(f88,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f59,f87])).
% 2.75/0.72  fof(f59,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f5])).
% 2.75/0.72  fof(f5,axiom,(
% 2.75/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.75/0.72  fof(f122,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1),X1))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f118,f120])).
% 2.75/0.72  fof(f120,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)),
% 2.75/0.72    inference(forward_demodulation,[],[f116,f109])).
% 2.75/0.72  fof(f116,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1)),
% 2.75/0.72    inference(superposition,[],[f91,f106])).
% 2.75/0.72  fof(f91,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f54,f87,f87])).
% 2.75/0.72  fof(f54,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f2])).
% 2.75/0.72  fof(f2,axiom,(
% 2.75/0.72    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.75/0.72  fof(f118,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),sK1),X1))) )),
% 2.75/0.72    inference(superposition,[],[f93,f106])).
% 2.75/0.72  fof(f93,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))))) )),
% 2.75/0.72    inference(definition_unfolding,[],[f74,f87,f87,f87,f87])).
% 2.75/0.72  fof(f74,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f12])).
% 2.75/0.72  fof(f12,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.75/0.72  fof(f404,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f400,f393])).
% 2.75/0.72  fof(f400,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(superposition,[],[f91,f172])).
% 2.75/0.72  fof(f711,plain,(
% 2.75/0.72    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f707,f393])).
% 2.75/0.72  fof(f707,plain,(
% 2.75/0.72    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(superposition,[],[f88,f393])).
% 2.75/0.72  fof(f677,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),k3_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))) )),
% 2.75/0.72    inference(superposition,[],[f225,f91])).
% 2.75/0.72  fof(f225,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X1))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f221,f55])).
% 2.75/0.72  fof(f221,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),X1))) )),
% 2.75/0.72    inference(superposition,[],[f93,f167])).
% 2.75/0.72  fof(f167,plain,(
% 2.75/0.72    k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) = k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1))),
% 2.75/0.72    inference(forward_demodulation,[],[f165,f137])).
% 2.75/0.72  fof(f137,plain,(
% 2.75/0.72    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(resolution,[],[f108,f67])).
% 2.75/0.72  fof(f165,plain,(
% 2.75/0.72    k4_subset_1(sK0,k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),sK1) = k3_tarski(k6_enumset1(k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),k3_subset_1(sK0,k4_xboole_0(sK0,sK1)),sK1))),
% 2.75/0.72    inference(resolution,[],[f124,f108])).
% 2.75/0.72  fof(f124,plain,(
% 2.75/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k3_tarski(k6_enumset1(k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),sK1))) )),
% 2.75/0.72    inference(resolution,[],[f98,f66])).
% 2.75/0.72  fof(f852,plain,(
% 2.75/0.72    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k1_xboole_0,X9))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f851,f147])).
% 2.75/0.72  fof(f851,plain,(
% 2.75/0.72    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),X9))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f752,f123])).
% 2.75/0.72  fof(f752,plain,(
% 2.75/0.72    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),X9))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f694,f712])).
% 2.75/0.72  fof(f694,plain,(
% 2.75/0.72    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9)),k3_xboole_0(sK1,X9)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),X9))) )),
% 2.75/0.72    inference(superposition,[],[f52,f225])).
% 2.75/0.72  fof(f52,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f11])).
% 2.75/0.72  fof(f11,axiom,(
% 2.75/0.72    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.75/0.72  fof(f53,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f7])).
% 2.75/0.72  fof(f7,axiom,(
% 2.75/0.72    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.75/0.72  fof(f1070,plain,(
% 2.75/0.72    ( ! [X6] : (k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = X6) )),
% 2.75/0.72    inference(forward_demodulation,[],[f1047,f90])).
% 2.75/0.72  fof(f1047,plain,(
% 2.75/0.72    ( ! [X6] : (k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k1_xboole_0)),k3_xboole_0(X6,k1_xboole_0))) )),
% 2.75/0.72    inference(superposition,[],[f88,f859])).
% 2.75/0.72  fof(f1300,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 2.75/0.72    inference(backward_demodulation,[],[f915,f1296])).
% 2.75/0.72  fof(f1296,plain,(
% 2.75/0.72    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(resolution,[],[f1264,f68])).
% 2.75/0.72  fof(f1264,plain,(
% 2.75/0.72    r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.75/0.72    inference(superposition,[],[f52,f712])).
% 2.75/0.72  fof(f915,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f914,f90])).
% 2.75/0.72  fof(f914,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f913,f207])).
% 2.75/0.72  fof(f207,plain,(
% 2.75/0.72    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f206,f55])).
% 2.75/0.72  fof(f206,plain,(
% 2.75/0.72    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f203,f197])).
% 2.75/0.72  fof(f197,plain,(
% 2.75/0.72    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(resolution,[],[f136,f46])).
% 2.75/0.72  fof(f136,plain,(
% 2.75/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k4_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(sK0,sK1)))) )),
% 2.75/0.72    inference(resolution,[],[f108,f94])).
% 2.75/0.72  fof(f203,plain,(
% 2.75/0.72    k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1))),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(superposition,[],[f91,f135])).
% 2.75/0.72  fof(f135,plain,(
% 2.75/0.72    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1))),
% 2.75/0.72    inference(resolution,[],[f108,f98])).
% 2.75/0.72  fof(f913,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f912,f135])).
% 2.75/0.72  fof(f912,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.75/0.72    inference(forward_demodulation,[],[f886,f55])).
% 2.75/0.72  fof(f886,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 2.75/0.72    inference(superposition,[],[f780,f90])).
% 2.75/0.72  fof(f780,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1))))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f208,f779])).
% 2.75/0.72  fof(f779,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f336,f778])).
% 2.75/0.72  fof(f778,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0))))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f777,f656])).
% 2.75/0.72  fof(f656,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)) = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1))))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f160,f655])).
% 2.75/0.72  fof(f655,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0)),
% 2.75/0.72    inference(forward_demodulation,[],[f654,f141])).
% 2.75/0.72  fof(f141,plain,(
% 2.75/0.72    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 2.75/0.72    inference(resolution,[],[f134,f68])).
% 2.75/0.72  fof(f134,plain,(
% 2.75/0.72    r1_xboole_0(k1_xboole_0,sK0)),
% 2.75/0.72    inference(superposition,[],[f52,f119])).
% 2.75/0.72  fof(f119,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.75/0.72    inference(forward_demodulation,[],[f115,f89])).
% 2.75/0.72  fof(f115,plain,(
% 2.75/0.72    k4_xboole_0(sK1,sK0) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(sK1,sK1))),
% 2.75/0.72    inference(superposition,[],[f88,f106])).
% 2.75/0.72  fof(f654,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k1_xboole_0,sK0))),
% 2.75/0.72    inference(forward_demodulation,[],[f646,f640])).
% 2.75/0.72  fof(f640,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k1_xboole_0)),
% 2.75/0.72    inference(superposition,[],[f90,f569])).
% 2.75/0.72  fof(f569,plain,(
% 2.75/0.72    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 2.75/0.72    inference(superposition,[],[f265,f169])).
% 2.75/0.72  fof(f169,plain,(
% 2.75/0.72    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.75/0.72    inference(resolution,[],[f168,f68])).
% 2.75/0.72  fof(f168,plain,(
% 2.75/0.72    r1_xboole_0(k1_xboole_0,sK1)),
% 2.75/0.72    inference(superposition,[],[f52,f148])).
% 2.75/0.72  fof(f148,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.75/0.72    inference(forward_demodulation,[],[f145,f89])).
% 2.75/0.72  fof(f145,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1)),
% 2.75/0.72    inference(superposition,[],[f88,f123])).
% 2.75/0.72  fof(f265,plain,(
% 2.75/0.72    ( ! [X1] : (k3_xboole_0(X1,sK1) = k3_xboole_0(sK0,k3_xboole_0(X1,sK1))) )),
% 2.75/0.72    inference(superposition,[],[f127,f55])).
% 2.75/0.72  fof(f127,plain,(
% 2.75/0.72    ( ! [X0] : (k3_xboole_0(sK1,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) )),
% 2.75/0.72    inference(superposition,[],[f75,f109])).
% 2.75/0.72  fof(f75,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f6])).
% 2.75/0.72  fof(f6,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.75/0.72  fof(f646,plain,(
% 2.75/0.72    k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)),k1_xboole_0)),
% 2.75/0.72    inference(superposition,[],[f91,f569])).
% 2.75/0.72  fof(f160,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),k3_xboole_0(sK0,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k1_xboole_0),X1))) )),
% 2.75/0.72    inference(superposition,[],[f93,f141])).
% 2.75/0.72  fof(f777,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0))))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f776,f147])).
% 2.75/0.72  fof(f776,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0))))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f739,f123])).
% 2.75/0.72  fof(f739,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,sK1),k3_xboole_0(sK1,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0))))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f668,f712])).
% 2.75/0.72  fof(f668,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)),k3_xboole_0(sK0,X0)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0)))),k3_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)),k3_xboole_0(k4_xboole_0(sK0,sK1),X0))))) )),
% 2.75/0.72    inference(superposition,[],[f225,f131])).
% 2.75/0.72  fof(f336,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)) = k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X1)),k3_xboole_0(k4_xboole_0(sK0,sK1),X1))))) )),
% 2.75/0.72    inference(superposition,[],[f93,f197])).
% 2.75/0.72  fof(f208,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1))) )),
% 2.75/0.72    inference(backward_demodulation,[],[f205,f207])).
% 2.75/0.72  fof(f205,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),X1))) )),
% 2.75/0.72    inference(forward_demodulation,[],[f201,f55])).
% 2.75/0.72  fof(f201,plain,(
% 2.75/0.72    ( ! [X1] : (k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k6_enumset1(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),X1)),k3_xboole_0(k4_xboole_0(k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)),X1))) )),
% 2.75/0.72    inference(superposition,[],[f93,f135])).
% 2.75/0.72  % SZS output end Proof for theBenchmark
% 2.75/0.72  % (5892)------------------------------
% 2.75/0.72  % (5892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.72  % (5892)Termination reason: Refutation
% 2.75/0.72  
% 2.75/0.72  % (5892)Memory used [KB]: 15223
% 2.75/0.72  % (5892)Time elapsed: 0.302 s
% 2.75/0.72  % (5892)------------------------------
% 2.75/0.72  % (5892)------------------------------
% 2.75/0.73  % (5883)Success in time 0.381 s
%------------------------------------------------------------------------------
