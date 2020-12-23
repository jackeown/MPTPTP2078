%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 137 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  259 ( 460 expanded)
%              Number of equality atoms :   68 ( 167 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f109,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK2(X0,X1,X2),X2)
              | ~ r2_hidden(sK2(X0,X1,X2),X1) )
            & ( r2_hidden(sK2(X0,X1,X2),X2)
              | r2_hidden(sK2(X0,X1,X2),X1) )
            & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X2)
          | ~ r2_hidden(sK2(X0,X1,X2),X1) )
        & ( r2_hidden(sK2(X0,X1,X2),X2)
          | r2_hidden(sK2(X0,X1,X2),X1) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f99,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2(X2,sK1,k1_xboole_0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2(X2,sK1,k1_xboole_0),k1_zfmisc_1(sK0))
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(resolution,[],[f95,f80])).

fof(f80,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X5,X4,k1_xboole_0),X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = X4
      | r2_hidden(sK2(X5,X4,k1_xboole_0),X4)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X5)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f68,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f67,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f67,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f58,f45,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | X1 = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f93,f69])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f66,f71])).

fof(f71,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f70,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (28155)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (28138)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (28155)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f109,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(resolution,[],[f99,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1)) & (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1)) & (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(sK2(X2,sK1,k1_xboole_0),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f98,f38])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(sK2(X2,sK1,k1_xboole_0),k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.47    inference(resolution,[],[f95,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X4,X5] : (r2_hidden(sK2(X5,X4,k1_xboole_0),X4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f40])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_xboole_0 = X4 | r2_hidden(sK2(X5,X4,k1_xboole_0),X4) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X5))) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X5)))) )),
% 0.21/0.47    inference(resolution,[],[f48,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f68,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.21/0.47    inference(superposition,[],[f67,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 0.21/0.47    inference(equality_resolution,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f58,f45,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f44,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.47    inference(flattening,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | X1 = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f69])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f37])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.47    inference(superposition,[],[f66,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f37])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(superposition,[],[f46,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(rectify,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28155)------------------------------
% 0.21/0.47  % (28155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28155)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28155)Memory used [KB]: 6268
% 0.21/0.47  % (28155)Time elapsed: 0.013 s
% 0.21/0.47  % (28155)------------------------------
% 0.21/0.47  % (28155)------------------------------
% 0.21/0.47  % (28127)Success in time 0.112 s
%------------------------------------------------------------------------------
