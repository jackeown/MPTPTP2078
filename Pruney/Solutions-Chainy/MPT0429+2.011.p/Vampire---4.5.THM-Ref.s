%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 171 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 442 expanded)
%              Number of equality atoms :   49 ( 122 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f117,f89,f274])).

fof(f274,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_xboole_0(X9,X9)
      | ~ r1_tarski(X11,X10) ) ),
    inference(subsumption_resolution,[],[f121,f248])).

fof(f248,plain,(
    ! [X3] : ~ r1_tarski(X3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f245,f126])).

fof(f126,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f92,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f92,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f245,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f227,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f227,plain,(
    sP0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f210,f146])).

fof(f146,plain,(
    ! [X5] :
      ( r1_tarski(sK2(k1_xboole_0,k1_xboole_0),X5)
      | sP0(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f128,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f70,f94])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f128,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0,k1_xboole_0),X0)
      | sP0(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f62,f126])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(sK2(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f210,plain,(
    ! [X7] : ~ r1_tarski(X7,sK1) ),
    inference(subsumption_resolution,[],[f207,f126])).

fof(f207,plain,(
    ! [X7] :
      ( r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(X7,sK1) ) ),
    inference(superposition,[],[f105,f195])).

fof(f195,plain,(
    k1_xboole_0 = k1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f190,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f190,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f163,f83])).

fof(f83,plain,(
    ~ m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(definition_unfolding,[],[f47,f82])).

fof(f47,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f37])).

fof(f37,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f163,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(superposition,[],[f85,f84])).

fof(f84,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f82,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              | k1_xboole_0 = X0
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              | k1_xboole_0 = X0
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_subset_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f61,f91])).

fof(f91,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f12,f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f121,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(k2_zfmisc_1(X9,X11),k1_xboole_0)
      | ~ r1_tarski(X11,X10)
      | ~ r1_xboole_0(X9,X9) ) ),
    inference(superposition,[],[f69,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f77,f55])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f89,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    ! [X0] : r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) ),
    inference(subsumption_resolution,[],[f90,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f90,plain,(
    ! [X0] :
      ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0)))
      | ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:44:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.49  % (22952)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.49  % (22954)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (22953)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (22979)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.50  % (22963)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (22963)Refutation not found, incomplete strategy% (22963)------------------------------
% 0.19/0.50  % (22963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (22963)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (22963)Memory used [KB]: 10618
% 0.19/0.50  % (22963)Time elapsed: 0.110 s
% 0.19/0.50  % (22963)------------------------------
% 0.19/0.50  % (22963)------------------------------
% 0.19/0.50  % (22958)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (22954)Refutation not found, incomplete strategy% (22954)------------------------------
% 0.19/0.50  % (22954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (22954)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (22954)Memory used [KB]: 10618
% 0.19/0.50  % (22954)Time elapsed: 0.110 s
% 0.19/0.50  % (22954)------------------------------
% 0.19/0.50  % (22954)------------------------------
% 0.19/0.50  % (22976)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (22952)Refutation not found, incomplete strategy% (22952)------------------------------
% 0.19/0.50  % (22952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (22952)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (22952)Memory used [KB]: 1663
% 0.19/0.50  % (22952)Time elapsed: 0.109 s
% 0.19/0.50  % (22952)------------------------------
% 0.19/0.50  % (22952)------------------------------
% 0.19/0.51  % (22959)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (22977)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (22968)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (22968)Refutation not found, incomplete strategy% (22968)------------------------------
% 0.19/0.52  % (22968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (22968)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (22968)Memory used [KB]: 6140
% 0.19/0.52  % (22968)Time elapsed: 0.084 s
% 0.19/0.52  % (22968)------------------------------
% 0.19/0.52  % (22968)------------------------------
% 0.19/0.52  % (22956)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (22966)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (22983)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (22960)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (22955)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (22970)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (22962)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (22970)Refutation not found, incomplete strategy% (22970)------------------------------
% 0.19/0.53  % (22970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22975)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (22962)Refutation not found, incomplete strategy% (22962)------------------------------
% 0.19/0.53  % (22962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22970)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (22970)Memory used [KB]: 10618
% 0.19/0.53  % (22970)Time elapsed: 0.136 s
% 0.19/0.53  % (22970)------------------------------
% 0.19/0.53  % (22970)------------------------------
% 0.19/0.53  % (22964)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (22975)Refutation not found, incomplete strategy% (22975)------------------------------
% 0.19/0.53  % (22975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22975)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (22975)Memory used [KB]: 10746
% 0.19/0.53  % (22975)Time elapsed: 0.138 s
% 0.19/0.53  % (22975)------------------------------
% 0.19/0.53  % (22975)------------------------------
% 0.19/0.53  % (22962)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (22962)Memory used [KB]: 10618
% 0.19/0.53  % (22962)Time elapsed: 0.135 s
% 0.19/0.53  % (22962)------------------------------
% 0.19/0.53  % (22962)------------------------------
% 0.19/0.53  % (22973)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (22964)Refutation not found, incomplete strategy% (22964)------------------------------
% 0.19/0.53  % (22964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22964)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (22964)Memory used [KB]: 10618
% 0.19/0.53  % (22964)Time elapsed: 0.133 s
% 0.19/0.53  % (22964)------------------------------
% 0.19/0.53  % (22964)------------------------------
% 0.19/0.53  % (22983)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f275,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f117,f89,f274])).
% 0.19/0.53  fof(f274,plain,(
% 0.19/0.53    ( ! [X10,X11,X9] : (~r1_xboole_0(X9,X9) | ~r1_tarski(X11,X10)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f121,f248])).
% 0.19/0.53  fof(f248,plain,(
% 0.19/0.53    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f245,f126])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(superposition,[],[f92,f94])).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.53    inference(resolution,[],[f56,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) )),
% 0.19/0.53    inference(equality_resolution,[],[f87])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) )),
% 0.19/0.53    inference(definition_unfolding,[],[f74,f82])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.53    inference(definition_unfolding,[],[f52,f81])).
% 0.19/0.53  fof(f81,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.53    inference(definition_unfolding,[],[f76,f79])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.19/0.53  fof(f74,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.19/0.53    inference(flattening,[],[f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.19/0.53    inference(nnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.19/0.53  fof(f245,plain,(
% 0.19/0.53    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | r2_hidden(X3,k1_xboole_0)) )),
% 0.19/0.53    inference(resolution,[],[f227,f61])).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f43])).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.19/0.53    inference(rectify,[],[f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.19/0.53    inference(nnf_transformation,[],[f35])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.53  fof(f227,plain,(
% 0.19/0.53    sP0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.53    inference(resolution,[],[f210,f146])).
% 0.19/0.53  fof(f146,plain,(
% 0.19/0.53    ( ! [X5] : (r1_tarski(sK2(k1_xboole_0,k1_xboole_0),X5) | sP0(k1_xboole_0,k1_xboole_0)) )),
% 0.19/0.53    inference(resolution,[],[f128,f102])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r1_tarski(X1,X0)) )),
% 0.19/0.53    inference(superposition,[],[f70,f94])).
% 0.19/0.53  fof(f70,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.19/0.53  fof(f128,plain,(
% 0.19/0.53    ( ! [X0] : (r1_tarski(sK2(X0,k1_xboole_0),X0) | sP0(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(resolution,[],[f62,f126])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_tarski(sK2(X0,X1),X0) | sP0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f43])).
% 0.19/0.53  fof(f210,plain,(
% 0.19/0.53    ( ! [X7] : (~r1_tarski(X7,sK1)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f207,f126])).
% 0.19/0.53  fof(f207,plain,(
% 0.19/0.53    ( ! [X7] : (r2_hidden(X7,k1_xboole_0) | ~r1_tarski(X7,sK1)) )),
% 0.19/0.53    inference(superposition,[],[f105,f195])).
% 0.19/0.53  fof(f195,plain,(
% 0.19/0.53    k1_xboole_0 = k1_zfmisc_1(sK1)),
% 0.19/0.53    inference(subsumption_resolution,[],[f190,f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,axiom,(
% 0.19/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.53  fof(f190,plain,(
% 0.19/0.53    k1_xboole_0 = k1_zfmisc_1(sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.19/0.53    inference(resolution,[],[f163,f83])).
% 0.19/0.53  fof(f83,plain,(
% 0.19/0.53    ~m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.19/0.53    inference(definition_unfolding,[],[f47,f82])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.19/0.53    inference(cnf_transformation,[],[f38])).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,negated_conjecture,(
% 0.19/0.53    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(negated_conjecture,[],[f22])).
% 0.19/0.53  fof(f22,conjecture,(
% 0.19/0.53    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.19/0.53  fof(f163,plain,(
% 0.19/0.53    ( ! [X0,X1] : (m1_subset_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) )),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f161])).
% 0.19/0.53  fof(f161,plain,(
% 0.19/0.53    ( ! [X0,X1] : (m1_subset_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.38/0.53    inference(superposition,[],[f85,f84])).
% 1.38/0.53  fof(f84,plain,(
% 1.38/0.53    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.38/0.53    inference(definition_unfolding,[],[f53,f82,f80])).
% 1.38/0.53  fof(f80,plain,(
% 1.38/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f8])).
% 1.38/0.53  fof(f8,axiom,(
% 1.38/0.53    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 1.38/0.53  fof(f53,plain,(
% 1.38/0.53    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,axiom,(
% 1.38/0.53    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).
% 1.38/0.53  fof(f85,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.38/0.53    inference(definition_unfolding,[],[f57,f67])).
% 1.38/0.53  fof(f67,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f11])).
% 1.38/0.53  fof(f11,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
% 1.38/0.53  fof(f57,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ! [X0,X1] : (! [X2] : (! [X3] : (m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.38/0.53    inference(flattening,[],[f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ! [X0,X1] : (! [X2] : (! [X3] : ((m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f20])).
% 1.38/0.53  fof(f20,axiom,(
% 1.38/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_subset_1)).
% 1.38/0.53  fof(f105,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(resolution,[],[f61,f91])).
% 1.38/0.53  fof(f91,plain,(
% 1.38/0.53    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 1.38/0.53    inference(equality_resolution,[],[f64])).
% 1.38/0.53  fof(f64,plain,(
% 1.38/0.53    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.38/0.53    inference(cnf_transformation,[],[f44])).
% 1.38/0.53  fof(f44,plain,(
% 1.38/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 1.38/0.53    inference(nnf_transformation,[],[f36])).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 1.38/0.53    inference(definition_folding,[],[f12,f35])).
% 1.38/0.53  fof(f12,axiom,(
% 1.38/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.38/0.53  fof(f121,plain,(
% 1.38/0.53    ( ! [X10,X11,X9] : (r1_tarski(k2_zfmisc_1(X9,X11),k1_xboole_0) | ~r1_tarski(X11,X10) | ~r1_xboole_0(X9,X9)) )),
% 1.38/0.53    inference(superposition,[],[f69,f111])).
% 1.38/0.53  fof(f111,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 1.38/0.53    inference(resolution,[],[f77,f55])).
% 1.38/0.53  fof(f77,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f34])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f14])).
% 1.38/0.53  fof(f14,axiom,(
% 1.38/0.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.38/0.53  fof(f69,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f30])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f13])).
% 1.38/0.53  fof(f13,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.38/0.53  fof(f89,plain,(
% 1.38/0.53    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.38/0.53    inference(equality_resolution,[],[f54])).
% 1.38/0.53  fof(f54,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f25])).
% 1.38/0.53  fof(f117,plain,(
% 1.38/0.53    ( ! [X0] : (r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0)))) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f90,f51])).
% 1.38/0.53  fof(f51,plain,(
% 1.38/0.53    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f16])).
% 1.38/0.53  fof(f16,axiom,(
% 1.38/0.53    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.38/0.53  fof(f90,plain,(
% 1.38/0.53    ( ! [X0] : (r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) | ~m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.38/0.53    inference(equality_resolution,[],[f59])).
% 1.38/0.53  fof(f59,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f39])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.53    inference(nnf_transformation,[],[f28])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f18])).
% 1.38/0.53  fof(f18,axiom,(
% 1.38/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (22983)------------------------------
% 1.38/0.53  % (22983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (22983)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (22983)Memory used [KB]: 1791
% 1.38/0.53  % (22983)Time elapsed: 0.137 s
% 1.38/0.53  % (22983)------------------------------
% 1.38/0.53  % (22983)------------------------------
% 1.38/0.53  % (22961)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.53  % (22973)Refutation not found, incomplete strategy% (22973)------------------------------
% 1.38/0.53  % (22973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (22973)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (22973)Memory used [KB]: 10746
% 1.38/0.53  % (22973)Time elapsed: 0.137 s
% 1.38/0.53  % (22973)------------------------------
% 1.38/0.53  % (22973)------------------------------
% 1.38/0.53  % (22974)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.53  % (22961)Refutation not found, incomplete strategy% (22961)------------------------------
% 1.38/0.53  % (22961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (22961)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (22961)Memory used [KB]: 10618
% 1.38/0.53  % (22961)Time elapsed: 0.132 s
% 1.38/0.53  % (22961)------------------------------
% 1.38/0.53  % (22961)------------------------------
% 1.38/0.53  % (22974)Refutation not found, incomplete strategy% (22974)------------------------------
% 1.38/0.53  % (22974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (22974)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (22974)Memory used [KB]: 1663
% 1.38/0.53  % (22974)Time elapsed: 0.151 s
% 1.38/0.53  % (22974)------------------------------
% 1.38/0.53  % (22974)------------------------------
% 1.38/0.53  % (22971)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.53  % (22969)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.53  % (22981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (22982)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (22965)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (22972)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (22950)Success in time 0.191 s
%------------------------------------------------------------------------------
