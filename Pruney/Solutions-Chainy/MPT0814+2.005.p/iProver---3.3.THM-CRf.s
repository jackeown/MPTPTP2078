%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:39 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 272 expanded)
%              Number of clauses        :   57 (  91 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 (1056 expanded)
%              Number of equality atoms :  112 ( 245 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK10)
          | ~ r2_hidden(X4,sK9)
          | k4_tarski(X4,X5) != sK8 )
      & r2_hidden(sK8,sK11)
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK10)
        | ~ r2_hidden(X4,sK9)
        | k4_tarski(X4,X5) != sK8 )
    & r2_hidden(sK8,sK11)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f16,f30])).

fof(f49,plain,(
    r2_hidden(sK8,sK11) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X5] :
          ( k4_tarski(X4,X5) = X3
          & m1_subset_1(X5,X1) )
     => ( k4_tarski(X4,sK7(X0,X1,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( k4_tarski(sK6(X0,X1,X3),X5) = X3
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6(X0,X1,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X3),X1)
        & m1_subset_1(sK6(X0,X1,X3),X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f10,f28,f27])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK10)
      | ~ r2_hidden(X4,sK9)
      | k4_tarski(X4,X5) != sK8 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f35,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X3),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X3),X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK8,sK11) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_703,plain,
    ( r2_hidden(sK8,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_702,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK6(X1,X2,X3),sK7(X1,X2,X3)) = X3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X3)
    | X0 != X3
    | k4_tarski(sK6(X4,X5,X2),sK7(X4,X5,X2)) = X2
    | k2_zfmisc_1(X4,X5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK6(X1,X2,X3),sK7(X1,X2,X3)) = X3 ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_701,plain,
    ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_4895,plain,
    ( k4_tarski(sK6(sK9,sK10,X0),sK7(sK9,sK10,X0)) = X0
    | r2_hidden(X0,sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_701])).

cnf(c_5067,plain,
    ( k4_tarski(sK6(sK9,sK10,sK8),sK7(sK9,sK10,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_703,c_4895])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK10)
    | k4_tarski(X0,X1) != sK8 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_704,plain,
    ( k4_tarski(X0,X1) != sK8
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5177,plain,
    ( r2_hidden(sK7(sK9,sK10,sK8),sK10) != iProver_top
    | r2_hidden(sK6(sK9,sK10,sK8),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5067,c_704])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_716,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_708,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_715,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1570,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_715])).

cnf(c_4660,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_1570])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1852,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_706])).

cnf(c_19,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( r2_hidden(sK8,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_849,plain,
    ( ~ r2_hidden(sK8,sK11)
    | ~ v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_850,plain,
    ( r2_hidden(sK8,sK11) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_895,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK9,sK10))
    | v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1200,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_1855,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_19,c_20,c_850,c_1200])).

cnf(c_4795,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4660,c_1855])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_707,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_960,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_715])).

cnf(c_1261,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_960])).

cnf(c_2634,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1855])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2295,plain,
    ( ~ m1_subset_1(sK7(sK9,sK10,sK8),sK10)
    | r2_hidden(sK7(sK9,sK10,sK8),sK10)
    | v1_xboole_0(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2296,plain,
    ( m1_subset_1(sK7(sK9,sK10,sK8),sK10) != iProver_top
    | r2_hidden(sK7(sK9,sK10,sK8),sK10) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2295])).

cnf(c_2292,plain,
    ( ~ m1_subset_1(sK6(sK9,sK10,sK8),sK9)
    | r2_hidden(sK6(sK9,sK10,sK8),sK9)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2293,plain,
    ( m1_subset_1(sK6(sK9,sK10,sK8),sK9) != iProver_top
    | r2_hidden(sK6(sK9,sK10,sK8),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2292])).

cnf(c_11,plain,
    ( m1_subset_1(sK7(X0,X1,X2),X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK7(X2,X3,X4),X3)
    | ~ r2_hidden(X4,X5)
    | X0 != X5
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK7(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_876,plain,
    ( m1_subset_1(sK7(X0,X1,sK8),X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(sK8,sK11) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_967,plain,
    ( m1_subset_1(sK7(sK9,sK10,sK8),sK10)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r2_hidden(sK8,sK11) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_968,plain,
    ( m1_subset_1(sK7(sK9,sK10,sK8),sK10) = iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | r2_hidden(sK8,sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_12,plain,
    ( m1_subset_1(sK6(X0,X1,X2),X0)
    | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK6(X2,X3,X4),X2)
    | ~ r2_hidden(X4,X5)
    | X0 != X5
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK6(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X0) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_871,plain,
    ( m1_subset_1(sK6(X0,X1,sK8),X0)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(sK8,sK11) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_964,plain,
    ( m1_subset_1(sK6(sK9,sK10,sK8),sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r2_hidden(sK8,sK11) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_965,plain,
    ( m1_subset_1(sK6(sK9,sK10,sK8),sK9) = iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | r2_hidden(sK8,sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5177,c_4795,c_2634,c_2296,c_2293,c_968,c_965,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.40/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.06  
% 1.40/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.40/1.06  
% 1.40/1.06  ------  iProver source info
% 1.40/1.06  
% 1.40/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.40/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.40/1.06  git: non_committed_changes: false
% 1.40/1.06  git: last_make_outside_of_git: false
% 1.40/1.06  
% 1.40/1.06  ------ 
% 1.40/1.06  
% 1.40/1.06  ------ Input Options
% 1.40/1.06  
% 1.40/1.06  --out_options                           all
% 1.40/1.06  --tptp_safe_out                         true
% 1.40/1.06  --problem_path                          ""
% 1.40/1.06  --include_path                          ""
% 1.40/1.06  --clausifier                            res/vclausify_rel
% 1.40/1.06  --clausifier_options                    --mode clausify
% 1.40/1.06  --stdin                                 false
% 1.40/1.06  --stats_out                             all
% 1.40/1.06  
% 1.40/1.06  ------ General Options
% 1.40/1.06  
% 1.40/1.06  --fof                                   false
% 1.40/1.06  --time_out_real                         305.
% 1.40/1.06  --time_out_virtual                      -1.
% 1.40/1.06  --symbol_type_check                     false
% 1.40/1.06  --clausify_out                          false
% 1.40/1.06  --sig_cnt_out                           false
% 1.40/1.06  --trig_cnt_out                          false
% 1.40/1.06  --trig_cnt_out_tolerance                1.
% 1.40/1.06  --trig_cnt_out_sk_spl                   false
% 1.40/1.06  --abstr_cl_out                          false
% 1.40/1.06  
% 1.40/1.06  ------ Global Options
% 1.40/1.06  
% 1.40/1.06  --schedule                              default
% 1.40/1.06  --add_important_lit                     false
% 1.40/1.06  --prop_solver_per_cl                    1000
% 1.40/1.06  --min_unsat_core                        false
% 1.40/1.06  --soft_assumptions                      false
% 1.40/1.06  --soft_lemma_size                       3
% 1.40/1.06  --prop_impl_unit_size                   0
% 1.40/1.06  --prop_impl_unit                        []
% 1.40/1.06  --share_sel_clauses                     true
% 1.40/1.06  --reset_solvers                         false
% 1.40/1.06  --bc_imp_inh                            [conj_cone]
% 1.40/1.06  --conj_cone_tolerance                   3.
% 1.40/1.06  --extra_neg_conj                        none
% 1.40/1.06  --large_theory_mode                     true
% 1.40/1.06  --prolific_symb_bound                   200
% 1.40/1.06  --lt_threshold                          2000
% 1.40/1.06  --clause_weak_htbl                      true
% 1.40/1.06  --gc_record_bc_elim                     false
% 1.40/1.06  
% 1.40/1.06  ------ Preprocessing Options
% 1.40/1.06  
% 1.40/1.06  --preprocessing_flag                    true
% 1.40/1.06  --time_out_prep_mult                    0.1
% 1.40/1.06  --splitting_mode                        input
% 1.40/1.06  --splitting_grd                         true
% 1.40/1.06  --splitting_cvd                         false
% 1.40/1.06  --splitting_cvd_svl                     false
% 1.40/1.06  --splitting_nvd                         32
% 1.40/1.06  --sub_typing                            true
% 1.40/1.06  --prep_gs_sim                           true
% 1.40/1.06  --prep_unflatten                        true
% 1.40/1.06  --prep_res_sim                          true
% 1.40/1.06  --prep_upred                            true
% 1.40/1.06  --prep_sem_filter                       exhaustive
% 1.40/1.06  --prep_sem_filter_out                   false
% 1.40/1.06  --pred_elim                             true
% 1.40/1.06  --res_sim_input                         true
% 1.40/1.06  --eq_ax_congr_red                       true
% 1.40/1.06  --pure_diseq_elim                       true
% 1.40/1.06  --brand_transform                       false
% 1.40/1.06  --non_eq_to_eq                          false
% 1.40/1.06  --prep_def_merge                        true
% 1.40/1.06  --prep_def_merge_prop_impl              false
% 1.40/1.06  --prep_def_merge_mbd                    true
% 1.40/1.06  --prep_def_merge_tr_red                 false
% 1.40/1.06  --prep_def_merge_tr_cl                  false
% 1.40/1.06  --smt_preprocessing                     true
% 1.40/1.06  --smt_ac_axioms                         fast
% 1.40/1.06  --preprocessed_out                      false
% 1.40/1.06  --preprocessed_stats                    false
% 1.40/1.06  
% 1.40/1.06  ------ Abstraction refinement Options
% 1.40/1.06  
% 1.40/1.06  --abstr_ref                             []
% 1.40/1.06  --abstr_ref_prep                        false
% 1.40/1.06  --abstr_ref_until_sat                   false
% 1.40/1.06  --abstr_ref_sig_restrict                funpre
% 1.40/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/1.06  --abstr_ref_under                       []
% 1.40/1.06  
% 1.40/1.06  ------ SAT Options
% 1.40/1.06  
% 1.40/1.06  --sat_mode                              false
% 1.40/1.06  --sat_fm_restart_options                ""
% 1.40/1.06  --sat_gr_def                            false
% 1.40/1.06  --sat_epr_types                         true
% 1.40/1.06  --sat_non_cyclic_types                  false
% 1.40/1.06  --sat_finite_models                     false
% 1.40/1.06  --sat_fm_lemmas                         false
% 1.40/1.06  --sat_fm_prep                           false
% 1.40/1.06  --sat_fm_uc_incr                        true
% 1.40/1.06  --sat_out_model                         small
% 1.40/1.06  --sat_out_clauses                       false
% 1.40/1.06  
% 1.40/1.06  ------ QBF Options
% 1.40/1.06  
% 1.40/1.06  --qbf_mode                              false
% 1.40/1.06  --qbf_elim_univ                         false
% 1.40/1.06  --qbf_dom_inst                          none
% 1.40/1.06  --qbf_dom_pre_inst                      false
% 1.40/1.06  --qbf_sk_in                             false
% 1.40/1.06  --qbf_pred_elim                         true
% 1.40/1.06  --qbf_split                             512
% 1.40/1.06  
% 1.40/1.06  ------ BMC1 Options
% 1.40/1.06  
% 1.40/1.06  --bmc1_incremental                      false
% 1.40/1.06  --bmc1_axioms                           reachable_all
% 1.40/1.06  --bmc1_min_bound                        0
% 1.40/1.06  --bmc1_max_bound                        -1
% 1.40/1.06  --bmc1_max_bound_default                -1
% 1.40/1.06  --bmc1_symbol_reachability              true
% 1.40/1.06  --bmc1_property_lemmas                  false
% 1.40/1.06  --bmc1_k_induction                      false
% 1.40/1.06  --bmc1_non_equiv_states                 false
% 1.40/1.06  --bmc1_deadlock                         false
% 1.40/1.06  --bmc1_ucm                              false
% 1.40/1.06  --bmc1_add_unsat_core                   none
% 1.40/1.06  --bmc1_unsat_core_children              false
% 1.40/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/1.06  --bmc1_out_stat                         full
% 1.40/1.06  --bmc1_ground_init                      false
% 1.40/1.06  --bmc1_pre_inst_next_state              false
% 1.40/1.06  --bmc1_pre_inst_state                   false
% 1.40/1.06  --bmc1_pre_inst_reach_state             false
% 1.40/1.06  --bmc1_out_unsat_core                   false
% 1.40/1.06  --bmc1_aig_witness_out                  false
% 1.40/1.06  --bmc1_verbose                          false
% 1.40/1.06  --bmc1_dump_clauses_tptp                false
% 1.40/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.40/1.06  --bmc1_dump_file                        -
% 1.40/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.40/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.40/1.06  --bmc1_ucm_extend_mode                  1
% 1.40/1.06  --bmc1_ucm_init_mode                    2
% 1.40/1.06  --bmc1_ucm_cone_mode                    none
% 1.40/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.40/1.06  --bmc1_ucm_relax_model                  4
% 1.40/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.40/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/1.06  --bmc1_ucm_layered_model                none
% 1.40/1.06  --bmc1_ucm_max_lemma_size               10
% 1.40/1.06  
% 1.40/1.06  ------ AIG Options
% 1.40/1.06  
% 1.40/1.06  --aig_mode                              false
% 1.40/1.06  
% 1.40/1.06  ------ Instantiation Options
% 1.40/1.06  
% 1.40/1.06  --instantiation_flag                    true
% 1.40/1.06  --inst_sos_flag                         false
% 1.40/1.06  --inst_sos_phase                        true
% 1.40/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/1.06  --inst_lit_sel_side                     num_symb
% 1.40/1.06  --inst_solver_per_active                1400
% 1.40/1.06  --inst_solver_calls_frac                1.
% 1.40/1.06  --inst_passive_queue_type               priority_queues
% 1.40/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/1.06  --inst_passive_queues_freq              [25;2]
% 1.40/1.06  --inst_dismatching                      true
% 1.40/1.06  --inst_eager_unprocessed_to_passive     true
% 1.40/1.06  --inst_prop_sim_given                   true
% 1.40/1.06  --inst_prop_sim_new                     false
% 1.40/1.06  --inst_subs_new                         false
% 1.40/1.06  --inst_eq_res_simp                      false
% 1.40/1.06  --inst_subs_given                       false
% 1.40/1.06  --inst_orphan_elimination               true
% 1.40/1.06  --inst_learning_loop_flag               true
% 1.40/1.06  --inst_learning_start                   3000
% 1.40/1.06  --inst_learning_factor                  2
% 1.40/1.06  --inst_start_prop_sim_after_learn       3
% 1.40/1.06  --inst_sel_renew                        solver
% 1.40/1.06  --inst_lit_activity_flag                true
% 1.40/1.06  --inst_restr_to_given                   false
% 1.40/1.06  --inst_activity_threshold               500
% 1.40/1.06  --inst_out_proof                        true
% 1.40/1.06  
% 1.40/1.06  ------ Resolution Options
% 1.40/1.06  
% 1.40/1.06  --resolution_flag                       true
% 1.40/1.06  --res_lit_sel                           adaptive
% 1.40/1.06  --res_lit_sel_side                      none
% 1.40/1.06  --res_ordering                          kbo
% 1.40/1.06  --res_to_prop_solver                    active
% 1.40/1.06  --res_prop_simpl_new                    false
% 1.40/1.06  --res_prop_simpl_given                  true
% 1.40/1.06  --res_passive_queue_type                priority_queues
% 1.40/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/1.06  --res_passive_queues_freq               [15;5]
% 1.40/1.06  --res_forward_subs                      full
% 1.40/1.06  --res_backward_subs                     full
% 1.40/1.06  --res_forward_subs_resolution           true
% 1.40/1.06  --res_backward_subs_resolution          true
% 1.40/1.06  --res_orphan_elimination                true
% 1.40/1.06  --res_time_limit                        2.
% 1.40/1.06  --res_out_proof                         true
% 1.40/1.06  
% 1.40/1.06  ------ Superposition Options
% 1.40/1.06  
% 1.40/1.06  --superposition_flag                    true
% 1.40/1.06  --sup_passive_queue_type                priority_queues
% 1.40/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.40/1.06  --demod_completeness_check              fast
% 1.40/1.06  --demod_use_ground                      true
% 1.40/1.06  --sup_to_prop_solver                    passive
% 1.40/1.06  --sup_prop_simpl_new                    true
% 1.40/1.06  --sup_prop_simpl_given                  true
% 1.40/1.06  --sup_fun_splitting                     false
% 1.40/1.06  --sup_smt_interval                      50000
% 1.40/1.07  
% 1.40/1.07  ------ Superposition Simplification Setup
% 1.40/1.07  
% 1.40/1.07  --sup_indices_passive                   []
% 1.40/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.07  --sup_full_bw                           [BwDemod]
% 1.40/1.07  --sup_immed_triv                        [TrivRules]
% 1.40/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.07  --sup_immed_bw_main                     []
% 1.40/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.07  
% 1.91/1.07  ------ Combination Options
% 1.91/1.07  
% 1.91/1.07  --comb_res_mult                         3
% 1.91/1.07  --comb_sup_mult                         2
% 1.91/1.07  --comb_inst_mult                        10
% 1.91/1.07  
% 1.91/1.07  ------ Debug Options
% 1.91/1.07  
% 1.91/1.07  --dbg_backtrace                         false
% 1.91/1.07  --dbg_dump_prop_clauses                 false
% 1.91/1.07  --dbg_dump_prop_clauses_file            -
% 1.91/1.07  --dbg_out_stat                          false
% 1.91/1.07  ------ Parsing...
% 1.91/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.07  
% 1.91/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.91/1.07  
% 1.91/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.07  
% 1.91/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.07  ------ Proving...
% 1.91/1.07  ------ Problem Properties 
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  clauses                                 18
% 1.91/1.07  conjectures                             3
% 1.91/1.07  EPR                                     3
% 1.91/1.07  Horn                                    13
% 1.91/1.07  unary                                   2
% 1.91/1.07  binary                                  5
% 1.91/1.07  lits                                    47
% 1.91/1.07  lits eq                                 9
% 1.91/1.07  fd_pure                                 0
% 1.91/1.07  fd_pseudo                               0
% 1.91/1.07  fd_cond                                 0
% 1.91/1.07  fd_pseudo_cond                          4
% 1.91/1.07  AC symbols                              0
% 1.91/1.07  
% 1.91/1.07  ------ Schedule dynamic 5 is on 
% 1.91/1.07  
% 1.91/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  ------ 
% 1.91/1.07  Current options:
% 1.91/1.07  ------ 
% 1.91/1.07  
% 1.91/1.07  ------ Input Options
% 1.91/1.07  
% 1.91/1.07  --out_options                           all
% 1.91/1.07  --tptp_safe_out                         true
% 1.91/1.07  --problem_path                          ""
% 1.91/1.07  --include_path                          ""
% 1.91/1.07  --clausifier                            res/vclausify_rel
% 1.91/1.07  --clausifier_options                    --mode clausify
% 1.91/1.07  --stdin                                 false
% 1.91/1.07  --stats_out                             all
% 1.91/1.07  
% 1.91/1.07  ------ General Options
% 1.91/1.07  
% 1.91/1.07  --fof                                   false
% 1.91/1.07  --time_out_real                         305.
% 1.91/1.07  --time_out_virtual                      -1.
% 1.91/1.07  --symbol_type_check                     false
% 1.91/1.07  --clausify_out                          false
% 1.91/1.07  --sig_cnt_out                           false
% 1.91/1.07  --trig_cnt_out                          false
% 1.91/1.07  --trig_cnt_out_tolerance                1.
% 1.91/1.07  --trig_cnt_out_sk_spl                   false
% 1.91/1.07  --abstr_cl_out                          false
% 1.91/1.07  
% 1.91/1.07  ------ Global Options
% 1.91/1.07  
% 1.91/1.07  --schedule                              default
% 1.91/1.07  --add_important_lit                     false
% 1.91/1.07  --prop_solver_per_cl                    1000
% 1.91/1.07  --min_unsat_core                        false
% 1.91/1.07  --soft_assumptions                      false
% 1.91/1.07  --soft_lemma_size                       3
% 1.91/1.07  --prop_impl_unit_size                   0
% 1.91/1.07  --prop_impl_unit                        []
% 1.91/1.07  --share_sel_clauses                     true
% 1.91/1.07  --reset_solvers                         false
% 1.91/1.07  --bc_imp_inh                            [conj_cone]
% 1.91/1.07  --conj_cone_tolerance                   3.
% 1.91/1.07  --extra_neg_conj                        none
% 1.91/1.07  --large_theory_mode                     true
% 1.91/1.07  --prolific_symb_bound                   200
% 1.91/1.07  --lt_threshold                          2000
% 1.91/1.07  --clause_weak_htbl                      true
% 1.91/1.07  --gc_record_bc_elim                     false
% 1.91/1.07  
% 1.91/1.07  ------ Preprocessing Options
% 1.91/1.07  
% 1.91/1.07  --preprocessing_flag                    true
% 1.91/1.07  --time_out_prep_mult                    0.1
% 1.91/1.07  --splitting_mode                        input
% 1.91/1.07  --splitting_grd                         true
% 1.91/1.07  --splitting_cvd                         false
% 1.91/1.07  --splitting_cvd_svl                     false
% 1.91/1.07  --splitting_nvd                         32
% 1.91/1.07  --sub_typing                            true
% 1.91/1.07  --prep_gs_sim                           true
% 1.91/1.07  --prep_unflatten                        true
% 1.91/1.07  --prep_res_sim                          true
% 1.91/1.07  --prep_upred                            true
% 1.91/1.07  --prep_sem_filter                       exhaustive
% 1.91/1.07  --prep_sem_filter_out                   false
% 1.91/1.07  --pred_elim                             true
% 1.91/1.07  --res_sim_input                         true
% 1.91/1.07  --eq_ax_congr_red                       true
% 1.91/1.07  --pure_diseq_elim                       true
% 1.91/1.07  --brand_transform                       false
% 1.91/1.07  --non_eq_to_eq                          false
% 1.91/1.07  --prep_def_merge                        true
% 1.91/1.07  --prep_def_merge_prop_impl              false
% 1.91/1.07  --prep_def_merge_mbd                    true
% 1.91/1.07  --prep_def_merge_tr_red                 false
% 1.91/1.07  --prep_def_merge_tr_cl                  false
% 1.91/1.07  --smt_preprocessing                     true
% 1.91/1.07  --smt_ac_axioms                         fast
% 1.91/1.07  --preprocessed_out                      false
% 1.91/1.07  --preprocessed_stats                    false
% 1.91/1.07  
% 1.91/1.07  ------ Abstraction refinement Options
% 1.91/1.07  
% 1.91/1.07  --abstr_ref                             []
% 1.91/1.07  --abstr_ref_prep                        false
% 1.91/1.07  --abstr_ref_until_sat                   false
% 1.91/1.07  --abstr_ref_sig_restrict                funpre
% 1.91/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.07  --abstr_ref_under                       []
% 1.91/1.07  
% 1.91/1.07  ------ SAT Options
% 1.91/1.07  
% 1.91/1.07  --sat_mode                              false
% 1.91/1.07  --sat_fm_restart_options                ""
% 1.91/1.07  --sat_gr_def                            false
% 1.91/1.07  --sat_epr_types                         true
% 1.91/1.07  --sat_non_cyclic_types                  false
% 1.91/1.07  --sat_finite_models                     false
% 1.91/1.07  --sat_fm_lemmas                         false
% 1.91/1.07  --sat_fm_prep                           false
% 1.91/1.07  --sat_fm_uc_incr                        true
% 1.91/1.07  --sat_out_model                         small
% 1.91/1.07  --sat_out_clauses                       false
% 1.91/1.07  
% 1.91/1.07  ------ QBF Options
% 1.91/1.07  
% 1.91/1.07  --qbf_mode                              false
% 1.91/1.07  --qbf_elim_univ                         false
% 1.91/1.07  --qbf_dom_inst                          none
% 1.91/1.07  --qbf_dom_pre_inst                      false
% 1.91/1.07  --qbf_sk_in                             false
% 1.91/1.07  --qbf_pred_elim                         true
% 1.91/1.07  --qbf_split                             512
% 1.91/1.07  
% 1.91/1.07  ------ BMC1 Options
% 1.91/1.07  
% 1.91/1.07  --bmc1_incremental                      false
% 1.91/1.07  --bmc1_axioms                           reachable_all
% 1.91/1.07  --bmc1_min_bound                        0
% 1.91/1.07  --bmc1_max_bound                        -1
% 1.91/1.07  --bmc1_max_bound_default                -1
% 1.91/1.07  --bmc1_symbol_reachability              true
% 1.91/1.07  --bmc1_property_lemmas                  false
% 1.91/1.07  --bmc1_k_induction                      false
% 1.91/1.07  --bmc1_non_equiv_states                 false
% 1.91/1.07  --bmc1_deadlock                         false
% 1.91/1.07  --bmc1_ucm                              false
% 1.91/1.07  --bmc1_add_unsat_core                   none
% 1.91/1.07  --bmc1_unsat_core_children              false
% 1.91/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.07  --bmc1_out_stat                         full
% 1.91/1.07  --bmc1_ground_init                      false
% 1.91/1.07  --bmc1_pre_inst_next_state              false
% 1.91/1.07  --bmc1_pre_inst_state                   false
% 1.91/1.07  --bmc1_pre_inst_reach_state             false
% 1.91/1.07  --bmc1_out_unsat_core                   false
% 1.91/1.07  --bmc1_aig_witness_out                  false
% 1.91/1.07  --bmc1_verbose                          false
% 1.91/1.07  --bmc1_dump_clauses_tptp                false
% 1.91/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.07  --bmc1_dump_file                        -
% 1.91/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.07  --bmc1_ucm_extend_mode                  1
% 1.91/1.07  --bmc1_ucm_init_mode                    2
% 1.91/1.07  --bmc1_ucm_cone_mode                    none
% 1.91/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.07  --bmc1_ucm_relax_model                  4
% 1.91/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.07  --bmc1_ucm_layered_model                none
% 1.91/1.07  --bmc1_ucm_max_lemma_size               10
% 1.91/1.07  
% 1.91/1.07  ------ AIG Options
% 1.91/1.07  
% 1.91/1.07  --aig_mode                              false
% 1.91/1.07  
% 1.91/1.07  ------ Instantiation Options
% 1.91/1.07  
% 1.91/1.07  --instantiation_flag                    true
% 1.91/1.07  --inst_sos_flag                         false
% 1.91/1.07  --inst_sos_phase                        true
% 1.91/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.07  --inst_lit_sel_side                     none
% 1.91/1.07  --inst_solver_per_active                1400
% 1.91/1.07  --inst_solver_calls_frac                1.
% 1.91/1.07  --inst_passive_queue_type               priority_queues
% 1.91/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.07  --inst_passive_queues_freq              [25;2]
% 1.91/1.07  --inst_dismatching                      true
% 1.91/1.07  --inst_eager_unprocessed_to_passive     true
% 1.91/1.07  --inst_prop_sim_given                   true
% 1.91/1.07  --inst_prop_sim_new                     false
% 1.91/1.07  --inst_subs_new                         false
% 1.91/1.07  --inst_eq_res_simp                      false
% 1.91/1.07  --inst_subs_given                       false
% 1.91/1.07  --inst_orphan_elimination               true
% 1.91/1.07  --inst_learning_loop_flag               true
% 1.91/1.07  --inst_learning_start                   3000
% 1.91/1.07  --inst_learning_factor                  2
% 1.91/1.07  --inst_start_prop_sim_after_learn       3
% 1.91/1.07  --inst_sel_renew                        solver
% 1.91/1.07  --inst_lit_activity_flag                true
% 1.91/1.07  --inst_restr_to_given                   false
% 1.91/1.07  --inst_activity_threshold               500
% 1.91/1.07  --inst_out_proof                        true
% 1.91/1.07  
% 1.91/1.07  ------ Resolution Options
% 1.91/1.07  
% 1.91/1.07  --resolution_flag                       false
% 1.91/1.07  --res_lit_sel                           adaptive
% 1.91/1.07  --res_lit_sel_side                      none
% 1.91/1.07  --res_ordering                          kbo
% 1.91/1.07  --res_to_prop_solver                    active
% 1.91/1.07  --res_prop_simpl_new                    false
% 1.91/1.07  --res_prop_simpl_given                  true
% 1.91/1.07  --res_passive_queue_type                priority_queues
% 1.91/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.07  --res_passive_queues_freq               [15;5]
% 1.91/1.07  --res_forward_subs                      full
% 1.91/1.07  --res_backward_subs                     full
% 1.91/1.07  --res_forward_subs_resolution           true
% 1.91/1.07  --res_backward_subs_resolution          true
% 1.91/1.07  --res_orphan_elimination                true
% 1.91/1.07  --res_time_limit                        2.
% 1.91/1.07  --res_out_proof                         true
% 1.91/1.07  
% 1.91/1.07  ------ Superposition Options
% 1.91/1.07  
% 1.91/1.07  --superposition_flag                    true
% 1.91/1.07  --sup_passive_queue_type                priority_queues
% 1.91/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.07  --demod_completeness_check              fast
% 1.91/1.07  --demod_use_ground                      true
% 1.91/1.07  --sup_to_prop_solver                    passive
% 1.91/1.07  --sup_prop_simpl_new                    true
% 1.91/1.07  --sup_prop_simpl_given                  true
% 1.91/1.07  --sup_fun_splitting                     false
% 1.91/1.07  --sup_smt_interval                      50000
% 1.91/1.07  
% 1.91/1.07  ------ Superposition Simplification Setup
% 1.91/1.07  
% 1.91/1.07  --sup_indices_passive                   []
% 1.91/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.07  --sup_full_bw                           [BwDemod]
% 1.91/1.07  --sup_immed_triv                        [TrivRules]
% 1.91/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.07  --sup_immed_bw_main                     []
% 1.91/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.07  
% 1.91/1.07  ------ Combination Options
% 1.91/1.07  
% 1.91/1.07  --comb_res_mult                         3
% 1.91/1.07  --comb_sup_mult                         2
% 1.91/1.07  --comb_inst_mult                        10
% 1.91/1.07  
% 1.91/1.07  ------ Debug Options
% 1.91/1.07  
% 1.91/1.07  --dbg_backtrace                         false
% 1.91/1.07  --dbg_dump_prop_clauses                 false
% 1.91/1.07  --dbg_dump_prop_clauses_file            -
% 1.91/1.07  --dbg_out_stat                          false
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  ------ Proving...
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  % SZS status Theorem for theBenchmark.p
% 1.91/1.07  
% 1.91/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.07  
% 1.91/1.07  fof(f7,conjecture,(
% 1.91/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f8,negated_conjecture,(
% 1.91/1.07    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.91/1.07    inference(negated_conjecture,[],[f7])).
% 1.91/1.07  
% 1.91/1.07  fof(f15,plain,(
% 1.91/1.07    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.91/1.07    inference(ennf_transformation,[],[f8])).
% 1.91/1.07  
% 1.91/1.07  fof(f16,plain,(
% 1.91/1.07    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.91/1.07    inference(flattening,[],[f15])).
% 1.91/1.07  
% 1.91/1.07  fof(f30,plain,(
% 1.91/1.07    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9) | k4_tarski(X4,X5) != sK8) & r2_hidden(sK8,sK11) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))))),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f31,plain,(
% 1.91/1.07    ! [X4,X5] : (~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9) | k4_tarski(X4,X5) != sK8) & r2_hidden(sK8,sK11) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 1.91/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f16,f30])).
% 1.91/1.07  
% 1.91/1.07  fof(f49,plain,(
% 1.91/1.07    r2_hidden(sK8,sK11)),
% 1.91/1.07    inference(cnf_transformation,[],[f31])).
% 1.91/1.07  
% 1.91/1.07  fof(f48,plain,(
% 1.91/1.07    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 1.91/1.07    inference(cnf_transformation,[],[f31])).
% 1.91/1.07  
% 1.91/1.07  fof(f3,axiom,(
% 1.91/1.07    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f10,plain,(
% 1.91/1.07    ! [X0,X1,X2,X3] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 1.91/1.07    inference(ennf_transformation,[],[f3])).
% 1.91/1.07  
% 1.91/1.07  fof(f28,plain,(
% 1.91/1.07    ( ! [X4] : (! [X3,X1,X0] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) => (k4_tarski(X4,sK7(X0,X1,X3)) = X3 & m1_subset_1(sK7(X0,X1,X3),X1)))) )),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f27,plain,(
% 1.91/1.07    ! [X3,X1,X0] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (k4_tarski(sK6(X0,X1,X3),X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(sK6(X0,X1,X3),X0)))),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f29,plain,(
% 1.91/1.07    ! [X0,X1,X2,X3] : (((k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 & m1_subset_1(sK7(X0,X1,X3),X1)) & m1_subset_1(sK6(X0,X1,X3),X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 1.91/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f10,f28,f27])).
% 1.91/1.07  
% 1.91/1.07  fof(f44,plain,(
% 1.91/1.07    ( ! [X2,X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f29])).
% 1.91/1.07  
% 1.91/1.07  fof(f6,axiom,(
% 1.91/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f9,plain,(
% 1.91/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.91/1.07    inference(unused_predicate_definition_removal,[],[f6])).
% 1.91/1.07  
% 1.91/1.07  fof(f14,plain,(
% 1.91/1.07    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.91/1.07    inference(ennf_transformation,[],[f9])).
% 1.91/1.07  
% 1.91/1.07  fof(f47,plain,(
% 1.91/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.91/1.07    inference(cnf_transformation,[],[f14])).
% 1.91/1.07  
% 1.91/1.07  fof(f50,plain,(
% 1.91/1.07    ( ! [X4,X5] : (~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9) | k4_tarski(X4,X5) != sK8) )),
% 1.91/1.07    inference(cnf_transformation,[],[f31])).
% 1.91/1.07  
% 1.91/1.07  fof(f1,axiom,(
% 1.91/1.07    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f17,plain,(
% 1.91/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.07    inference(nnf_transformation,[],[f1])).
% 1.91/1.07  
% 1.91/1.07  fof(f18,plain,(
% 1.91/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.07    inference(rectify,[],[f17])).
% 1.91/1.07  
% 1.91/1.07  fof(f19,plain,(
% 1.91/1.07    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f20,plain,(
% 1.91/1.07    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.91/1.07  
% 1.91/1.07  fof(f33,plain,(
% 1.91/1.07    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f20])).
% 1.91/1.07  
% 1.91/1.07  fof(f2,axiom,(
% 1.91/1.07    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f21,plain,(
% 1.91/1.07    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.91/1.07    inference(nnf_transformation,[],[f2])).
% 1.91/1.07  
% 1.91/1.07  fof(f22,plain,(
% 1.91/1.07    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.91/1.07    inference(rectify,[],[f21])).
% 1.91/1.07  
% 1.91/1.07  fof(f25,plain,(
% 1.91/1.07    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f24,plain,(
% 1.91/1.07    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f23,plain,(
% 1.91/1.07    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.91/1.07    introduced(choice_axiom,[])).
% 1.91/1.07  
% 1.91/1.07  fof(f26,plain,(
% 1.91/1.07    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.91/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.91/1.07  
% 1.91/1.07  fof(f35,plain,(
% 1.91/1.07    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.91/1.07    inference(cnf_transformation,[],[f26])).
% 1.91/1.07  
% 1.91/1.07  fof(f54,plain,(
% 1.91/1.07    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.91/1.07    inference(equality_resolution,[],[f35])).
% 1.91/1.07  
% 1.91/1.07  fof(f32,plain,(
% 1.91/1.07    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f20])).
% 1.91/1.07  
% 1.91/1.07  fof(f4,axiom,(
% 1.91/1.07    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f11,plain,(
% 1.91/1.07    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.91/1.07    inference(ennf_transformation,[],[f4])).
% 1.91/1.07  
% 1.91/1.07  fof(f45,plain,(
% 1.91/1.07    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f11])).
% 1.91/1.07  
% 1.91/1.07  fof(f34,plain,(
% 1.91/1.07    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.91/1.07    inference(cnf_transformation,[],[f26])).
% 1.91/1.07  
% 1.91/1.07  fof(f55,plain,(
% 1.91/1.07    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.91/1.07    inference(equality_resolution,[],[f34])).
% 1.91/1.07  
% 1.91/1.07  fof(f5,axiom,(
% 1.91/1.07    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.91/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.07  
% 1.91/1.07  fof(f12,plain,(
% 1.91/1.07    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.91/1.07    inference(ennf_transformation,[],[f5])).
% 1.91/1.07  
% 1.91/1.07  fof(f13,plain,(
% 1.91/1.07    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.91/1.07    inference(flattening,[],[f12])).
% 1.91/1.07  
% 1.91/1.07  fof(f46,plain,(
% 1.91/1.07    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f13])).
% 1.91/1.07  
% 1.91/1.07  fof(f43,plain,(
% 1.91/1.07    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X3),X1) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f29])).
% 1.91/1.07  
% 1.91/1.07  fof(f42,plain,(
% 1.91/1.07    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X3),X0) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 1.91/1.07    inference(cnf_transformation,[],[f29])).
% 1.91/1.07  
% 1.91/1.07  cnf(c_17,negated_conjecture,
% 1.91/1.07      ( r2_hidden(sK8,sK11) ),
% 1.91/1.07      inference(cnf_transformation,[],[f49]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_703,plain,
% 1.91/1.07      ( r2_hidden(sK8,sK11) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_18,negated_conjecture,
% 1.91/1.07      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
% 1.91/1.07      inference(cnf_transformation,[],[f48]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_702,plain,
% 1.91/1.07      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_10,plain,
% 1.91/1.07      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 1.91/1.07      | ~ r2_hidden(X3,X0)
% 1.91/1.07      | k4_tarski(sK6(X1,X2,X3),sK7(X1,X2,X3)) = X3 ),
% 1.91/1.07      inference(cnf_transformation,[],[f44]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_15,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.91/1.07      inference(cnf_transformation,[],[f47]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_218,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.07      | ~ r2_hidden(X2,X3)
% 1.91/1.07      | X0 != X3
% 1.91/1.07      | k4_tarski(sK6(X4,X5,X2),sK7(X4,X5,X2)) = X2
% 1.91/1.07      | k2_zfmisc_1(X4,X5) != X1 ),
% 1.91/1.07      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_219,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.07      | ~ r2_hidden(X3,X0)
% 1.91/1.07      | k4_tarski(sK6(X1,X2,X3),sK7(X1,X2,X3)) = X3 ),
% 1.91/1.07      inference(unflattening,[status(thm)],[c_218]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_701,plain,
% 1.91/1.07      ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
% 1.91/1.07      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.91/1.07      | r2_hidden(X2,X3) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_4895,plain,
% 1.91/1.07      ( k4_tarski(sK6(sK9,sK10,X0),sK7(sK9,sK10,X0)) = X0
% 1.91/1.07      | r2_hidden(X0,sK11) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_702,c_701]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_5067,plain,
% 1.91/1.07      ( k4_tarski(sK6(sK9,sK10,sK8),sK7(sK9,sK10,sK8)) = sK8 ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_703,c_4895]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_16,negated_conjecture,
% 1.91/1.07      ( ~ r2_hidden(X0,sK9)
% 1.91/1.07      | ~ r2_hidden(X1,sK10)
% 1.91/1.07      | k4_tarski(X0,X1) != sK8 ),
% 1.91/1.07      inference(cnf_transformation,[],[f50]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_704,plain,
% 1.91/1.07      ( k4_tarski(X0,X1) != sK8
% 1.91/1.07      | r2_hidden(X0,sK9) != iProver_top
% 1.91/1.07      | r2_hidden(X1,sK10) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_5177,plain,
% 1.91/1.07      ( r2_hidden(sK7(sK9,sK10,sK8),sK10) != iProver_top
% 1.91/1.07      | r2_hidden(sK6(sK9,sK10,sK8),sK9) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_5067,c_704]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_0,plain,
% 1.91/1.07      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.91/1.07      inference(cnf_transformation,[],[f33]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_716,plain,
% 1.91/1.07      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.91/1.07      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_8,plain,
% 1.91/1.07      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 1.91/1.07      | r2_hidden(sK5(X1,X2,X0),X2) ),
% 1.91/1.07      inference(cnf_transformation,[],[f54]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_708,plain,
% 1.91/1.07      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.91/1.07      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1,plain,
% 1.91/1.07      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.91/1.07      inference(cnf_transformation,[],[f32]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_715,plain,
% 1.91/1.07      ( r2_hidden(X0,X1) != iProver_top
% 1.91/1.07      | v1_xboole_0(X1) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1570,plain,
% 1.91/1.07      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.91/1.07      | v1_xboole_0(X2) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_708,c_715]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_4660,plain,
% 1.91/1.07      ( v1_xboole_0(X0) != iProver_top
% 1.91/1.07      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_716,c_1570]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_13,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.07      | ~ v1_xboole_0(X1)
% 1.91/1.07      | v1_xboole_0(X0) ),
% 1.91/1.07      inference(cnf_transformation,[],[f45]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_706,plain,
% 1.91/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.91/1.07      | v1_xboole_0(X1) != iProver_top
% 1.91/1.07      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1852,plain,
% 1.91/1.07      ( v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top
% 1.91/1.07      | v1_xboole_0(sK11) = iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_702,c_706]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_19,plain,
% 1.91/1.07      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_20,plain,
% 1.91/1.07      ( r2_hidden(sK8,sK11) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_849,plain,
% 1.91/1.07      ( ~ r2_hidden(sK8,sK11) | ~ v1_xboole_0(sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_850,plain,
% 1.91/1.07      ( r2_hidden(sK8,sK11) != iProver_top
% 1.91/1.07      | v1_xboole_0(sK11) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_895,plain,
% 1.91/1.07      ( ~ m1_subset_1(sK11,k1_zfmisc_1(X0))
% 1.91/1.07      | ~ v1_xboole_0(X0)
% 1.91/1.07      | v1_xboole_0(sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_13]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1199,plain,
% 1.91/1.07      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 1.91/1.07      | ~ v1_xboole_0(k2_zfmisc_1(sK9,sK10))
% 1.91/1.07      | v1_xboole_0(sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_895]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1200,plain,
% 1.91/1.07      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 1.91/1.07      | v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top
% 1.91/1.07      | v1_xboole_0(sK11) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1855,plain,
% 1.91/1.07      ( v1_xboole_0(k2_zfmisc_1(sK9,sK10)) != iProver_top ),
% 1.91/1.07      inference(global_propositional_subsumption,
% 1.91/1.07                [status(thm)],
% 1.91/1.07                [c_1852,c_19,c_20,c_850,c_1200]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_4795,plain,
% 1.91/1.07      ( v1_xboole_0(sK10) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_4660,c_1855]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_9,plain,
% 1.91/1.07      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 1.91/1.07      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 1.91/1.07      inference(cnf_transformation,[],[f55]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_707,plain,
% 1.91/1.07      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.91/1.07      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_960,plain,
% 1.91/1.07      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.91/1.07      | v1_xboole_0(X1) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_707,c_715]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_1261,plain,
% 1.91/1.07      ( v1_xboole_0(X0) != iProver_top
% 1.91/1.07      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_716,c_960]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_2634,plain,
% 1.91/1.07      ( v1_xboole_0(sK9) != iProver_top ),
% 1.91/1.07      inference(superposition,[status(thm)],[c_1261,c_1855]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_14,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.91/1.07      inference(cnf_transformation,[],[f46]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_2295,plain,
% 1.91/1.07      ( ~ m1_subset_1(sK7(sK9,sK10,sK8),sK10)
% 1.91/1.07      | r2_hidden(sK7(sK9,sK10,sK8),sK10)
% 1.91/1.07      | v1_xboole_0(sK10) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_14]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_2296,plain,
% 1.91/1.07      ( m1_subset_1(sK7(sK9,sK10,sK8),sK10) != iProver_top
% 1.91/1.07      | r2_hidden(sK7(sK9,sK10,sK8),sK10) = iProver_top
% 1.91/1.07      | v1_xboole_0(sK10) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_2295]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_2292,plain,
% 1.91/1.07      ( ~ m1_subset_1(sK6(sK9,sK10,sK8),sK9)
% 1.91/1.07      | r2_hidden(sK6(sK9,sK10,sK8),sK9)
% 1.91/1.07      | v1_xboole_0(sK9) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_14]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_2293,plain,
% 1.91/1.07      ( m1_subset_1(sK6(sK9,sK10,sK8),sK9) != iProver_top
% 1.91/1.07      | r2_hidden(sK6(sK9,sK10,sK8),sK9) = iProver_top
% 1.91/1.07      | v1_xboole_0(sK9) = iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_2292]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_11,plain,
% 1.91/1.07      ( m1_subset_1(sK7(X0,X1,X2),X1)
% 1.91/1.07      | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1))
% 1.91/1.07      | ~ r2_hidden(X2,X3) ),
% 1.91/1.07      inference(cnf_transformation,[],[f43]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_248,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.07      | m1_subset_1(sK7(X2,X3,X4),X3)
% 1.91/1.07      | ~ r2_hidden(X4,X5)
% 1.91/1.07      | X0 != X5
% 1.91/1.07      | k2_zfmisc_1(X2,X3) != X1 ),
% 1.91/1.07      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_249,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.07      | m1_subset_1(sK7(X1,X2,X3),X2)
% 1.91/1.07      | ~ r2_hidden(X3,X0) ),
% 1.91/1.07      inference(unflattening,[status(thm)],[c_248]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_876,plain,
% 1.91/1.07      ( m1_subset_1(sK7(X0,X1,sK8),X1)
% 1.91/1.07      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.91/1.07      | ~ r2_hidden(sK8,sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_249]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_967,plain,
% 1.91/1.07      ( m1_subset_1(sK7(sK9,sK10,sK8),sK10)
% 1.91/1.07      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 1.91/1.07      | ~ r2_hidden(sK8,sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_876]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_968,plain,
% 1.91/1.07      ( m1_subset_1(sK7(sK9,sK10,sK8),sK10) = iProver_top
% 1.91/1.07      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 1.91/1.07      | r2_hidden(sK8,sK11) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_12,plain,
% 1.91/1.07      ( m1_subset_1(sK6(X0,X1,X2),X0)
% 1.91/1.07      | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1))
% 1.91/1.07      | ~ r2_hidden(X2,X3) ),
% 1.91/1.07      inference(cnf_transformation,[],[f42]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_233,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.07      | m1_subset_1(sK6(X2,X3,X4),X2)
% 1.91/1.07      | ~ r2_hidden(X4,X5)
% 1.91/1.07      | X0 != X5
% 1.91/1.07      | k2_zfmisc_1(X2,X3) != X1 ),
% 1.91/1.07      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_234,plain,
% 1.91/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.07      | m1_subset_1(sK6(X1,X2,X3),X1)
% 1.91/1.07      | ~ r2_hidden(X3,X0) ),
% 1.91/1.07      inference(unflattening,[status(thm)],[c_233]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_871,plain,
% 1.91/1.07      ( m1_subset_1(sK6(X0,X1,sK8),X0)
% 1.91/1.07      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.91/1.07      | ~ r2_hidden(sK8,sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_234]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_964,plain,
% 1.91/1.07      ( m1_subset_1(sK6(sK9,sK10,sK8),sK9)
% 1.91/1.07      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 1.91/1.07      | ~ r2_hidden(sK8,sK11) ),
% 1.91/1.07      inference(instantiation,[status(thm)],[c_871]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(c_965,plain,
% 1.91/1.07      ( m1_subset_1(sK6(sK9,sK10,sK8),sK9) = iProver_top
% 1.91/1.07      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 1.91/1.07      | r2_hidden(sK8,sK11) != iProver_top ),
% 1.91/1.07      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 1.91/1.07  
% 1.91/1.07  cnf(contradiction,plain,
% 1.91/1.07      ( $false ),
% 1.91/1.07      inference(minisat,
% 1.91/1.07                [status(thm)],
% 1.91/1.07                [c_5177,c_4795,c_2634,c_2296,c_2293,c_968,c_965,c_20,
% 1.91/1.07                 c_19]) ).
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.07  
% 1.91/1.07  ------                               Statistics
% 1.91/1.07  
% 1.91/1.07  ------ General
% 1.91/1.07  
% 1.91/1.07  abstr_ref_over_cycles:                  0
% 1.91/1.07  abstr_ref_under_cycles:                 0
% 1.91/1.07  gc_basic_clause_elim:                   0
% 1.91/1.07  forced_gc_time:                         0
% 1.91/1.07  parsing_time:                           0.012
% 1.91/1.07  unif_index_cands_time:                  0.
% 1.91/1.07  unif_index_add_time:                    0.
% 1.91/1.07  orderings_time:                         0.
% 1.91/1.07  out_proof_time:                         0.007
% 1.91/1.07  total_time:                             0.25
% 1.91/1.07  num_of_symbols:                         50
% 1.91/1.07  num_of_terms:                           7183
% 1.91/1.07  
% 1.91/1.07  ------ Preprocessing
% 1.91/1.07  
% 1.91/1.07  num_of_splits:                          0
% 1.91/1.07  num_of_split_atoms:                     0
% 1.91/1.07  num_of_reused_defs:                     0
% 1.91/1.07  num_eq_ax_congr_red:                    70
% 1.91/1.07  num_of_sem_filtered_clauses:            1
% 1.91/1.07  num_of_subtypes:                        0
% 1.91/1.07  monotx_restored_types:                  0
% 1.91/1.07  sat_num_of_epr_types:                   0
% 1.91/1.07  sat_num_of_non_cyclic_types:            0
% 1.91/1.07  sat_guarded_non_collapsed_types:        0
% 1.91/1.07  num_pure_diseq_elim:                    0
% 1.91/1.07  simp_replaced_by:                       0
% 1.91/1.07  res_preprocessed:                       88
% 1.91/1.07  prep_upred:                             0
% 1.91/1.07  prep_unflattend:                        6
% 1.91/1.07  smt_new_axioms:                         0
% 1.91/1.07  pred_elim_cands:                        3
% 1.91/1.07  pred_elim:                              1
% 1.91/1.07  pred_elim_cl:                           1
% 1.91/1.07  pred_elim_cycles:                       3
% 1.91/1.07  merged_defs:                            0
% 1.91/1.07  merged_defs_ncl:                        0
% 1.91/1.07  bin_hyper_res:                          0
% 1.91/1.07  prep_cycles:                            4
% 1.91/1.07  pred_elim_time:                         0.002
% 1.91/1.07  splitting_time:                         0.
% 1.91/1.07  sem_filter_time:                        0.
% 1.91/1.07  monotx_time:                            0.001
% 1.91/1.07  subtype_inf_time:                       0.
% 1.91/1.07  
% 1.91/1.07  ------ Problem properties
% 1.91/1.07  
% 1.91/1.07  clauses:                                18
% 1.91/1.07  conjectures:                            3
% 1.91/1.07  epr:                                    3
% 1.91/1.07  horn:                                   13
% 1.91/1.07  ground:                                 2
% 1.91/1.07  unary:                                  2
% 1.91/1.07  binary:                                 5
% 1.91/1.07  lits:                                   47
% 1.91/1.07  lits_eq:                                9
% 1.91/1.07  fd_pure:                                0
% 1.91/1.07  fd_pseudo:                              0
% 1.91/1.07  fd_cond:                                0
% 1.91/1.07  fd_pseudo_cond:                         4
% 1.91/1.07  ac_symbols:                             0
% 1.91/1.07  
% 1.91/1.07  ------ Propositional Solver
% 1.91/1.07  
% 1.91/1.07  prop_solver_calls:                      28
% 1.91/1.07  prop_fast_solver_calls:                 561
% 1.91/1.07  smt_solver_calls:                       0
% 1.91/1.07  smt_fast_solver_calls:                  0
% 1.91/1.07  prop_num_of_clauses:                    2615
% 1.91/1.07  prop_preprocess_simplified:             6349
% 1.91/1.07  prop_fo_subsumed:                       2
% 1.91/1.07  prop_solver_time:                       0.
% 1.91/1.07  smt_solver_time:                        0.
% 1.91/1.07  smt_fast_solver_time:                   0.
% 1.91/1.07  prop_fast_solver_time:                  0.
% 1.91/1.07  prop_unsat_core_time:                   0.
% 1.91/1.07  
% 1.91/1.07  ------ QBF
% 1.91/1.07  
% 1.91/1.07  qbf_q_res:                              0
% 1.91/1.07  qbf_num_tautologies:                    0
% 1.91/1.07  qbf_prep_cycles:                        0
% 1.91/1.07  
% 1.91/1.07  ------ BMC1
% 1.91/1.07  
% 1.91/1.07  bmc1_current_bound:                     -1
% 1.91/1.07  bmc1_last_solved_bound:                 -1
% 1.91/1.07  bmc1_unsat_core_size:                   -1
% 1.91/1.07  bmc1_unsat_core_parents_size:           -1
% 1.91/1.07  bmc1_merge_next_fun:                    0
% 1.91/1.07  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.07  
% 1.91/1.07  ------ Instantiation
% 1.91/1.07  
% 1.91/1.07  inst_num_of_clauses:                    776
% 1.91/1.07  inst_num_in_passive:                    339
% 1.91/1.07  inst_num_in_active:                     171
% 1.91/1.07  inst_num_in_unprocessed:                266
% 1.91/1.07  inst_num_of_loops:                      200
% 1.91/1.07  inst_num_of_learning_restarts:          0
% 1.91/1.07  inst_num_moves_active_passive:          27
% 1.91/1.07  inst_lit_activity:                      0
% 1.91/1.07  inst_lit_activity_moves:                1
% 1.91/1.07  inst_num_tautologies:                   0
% 1.91/1.07  inst_num_prop_implied:                  0
% 1.91/1.07  inst_num_existing_simplified:           0
% 1.91/1.07  inst_num_eq_res_simplified:             0
% 1.91/1.07  inst_num_child_elim:                    0
% 1.91/1.07  inst_num_of_dismatching_blockings:      78
% 1.91/1.07  inst_num_of_non_proper_insts:           278
% 1.91/1.07  inst_num_of_duplicates:                 0
% 1.91/1.07  inst_inst_num_from_inst_to_res:         0
% 1.91/1.07  inst_dismatching_checking_time:         0.
% 1.91/1.07  
% 1.91/1.07  ------ Resolution
% 1.91/1.07  
% 1.91/1.07  res_num_of_clauses:                     0
% 1.91/1.07  res_num_in_passive:                     0
% 1.91/1.07  res_num_in_active:                      0
% 1.91/1.07  res_num_of_loops:                       92
% 1.91/1.07  res_forward_subset_subsumed:            4
% 1.91/1.07  res_backward_subset_subsumed:           0
% 1.91/1.07  res_forward_subsumed:                   0
% 1.91/1.07  res_backward_subsumed:                  0
% 1.91/1.07  res_forward_subsumption_resolution:     0
% 1.91/1.07  res_backward_subsumption_resolution:    0
% 1.91/1.07  res_clause_to_clause_subsumption:       222
% 1.91/1.07  res_orphan_elimination:                 0
% 1.91/1.07  res_tautology_del:                      2
% 1.91/1.07  res_num_eq_res_simplified:              0
% 1.91/1.07  res_num_sel_changes:                    0
% 1.91/1.07  res_moves_from_active_to_pass:          0
% 1.91/1.07  
% 1.91/1.07  ------ Superposition
% 1.91/1.07  
% 1.91/1.07  sup_time_total:                         0.
% 1.91/1.07  sup_time_generating:                    0.
% 1.91/1.07  sup_time_sim_full:                      0.
% 1.91/1.07  sup_time_sim_immed:                     0.
% 1.91/1.07  
% 1.91/1.07  sup_num_of_clauses:                     99
% 1.91/1.07  sup_num_in_active:                      39
% 1.91/1.07  sup_num_in_passive:                     60
% 1.91/1.07  sup_num_of_loops:                       38
% 1.91/1.07  sup_fw_superposition:                   45
% 1.91/1.07  sup_bw_superposition:                   43
% 1.91/1.07  sup_immediate_simplified:               5
% 1.91/1.07  sup_given_eliminated:                   0
% 1.91/1.07  comparisons_done:                       0
% 1.91/1.07  comparisons_avoided:                    2
% 1.91/1.07  
% 1.91/1.07  ------ Simplifications
% 1.91/1.07  
% 1.91/1.07  
% 1.91/1.07  sim_fw_subset_subsumed:                 1
% 1.91/1.07  sim_bw_subset_subsumed:                 0
% 1.91/1.07  sim_fw_subsumed:                        4
% 1.91/1.07  sim_bw_subsumed:                        0
% 1.91/1.07  sim_fw_subsumption_res:                 0
% 1.91/1.07  sim_bw_subsumption_res:                 0
% 1.91/1.07  sim_tautology_del:                      3
% 1.91/1.07  sim_eq_tautology_del:                   0
% 1.91/1.07  sim_eq_res_simp:                        0
% 1.91/1.07  sim_fw_demodulated:                     0
% 1.91/1.07  sim_bw_demodulated:                     0
% 1.91/1.07  sim_light_normalised:                   0
% 1.91/1.07  sim_joinable_taut:                      0
% 1.91/1.07  sim_joinable_simp:                      0
% 1.91/1.07  sim_ac_normalised:                      0
% 1.91/1.07  sim_smt_subsumption:                    0
% 1.91/1.07  
%------------------------------------------------------------------------------
