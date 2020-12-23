%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:56 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 228 expanded)
%              Number of clauses        :   66 (  75 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  440 (1193 expanded)
%              Number of equality atoms :  100 ( 182 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK7 != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK7) )
              & ( r2_hidden(X3,sK7)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK6 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK6)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK6) ) )
              | ~ m1_subset_1(X3,sK5) )
          & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK6 != sK7
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK6)
            | ~ r2_hidden(X3,sK7) )
          & ( r2_hidden(X3,sK7)
            | ~ r2_hidden(X3,sK6) ) )
        | ~ m1_subset_1(X3,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f34,f33])).

fof(f57,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK7)
      | ~ r2_hidden(X3,sK6)
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK6)
      | ~ r2_hidden(X3,sK7)
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_139,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_3])).

cnf(c_140,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_10406,plain,
    ( m1_subset_1(sK0(sK7,sK6),X0)
    | ~ r2_hidden(sK0(sK7,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_10408,plain,
    ( m1_subset_1(sK0(sK7,sK6),sK5)
    | ~ r2_hidden(sK0(sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_10406])).

cnf(c_373,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5945,plain,
    ( X0 != X1
    | X0 = k3_tarski(k1_zfmisc_1(sK5))
    | k3_tarski(k1_zfmisc_1(sK5)) != X1 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_5946,plain,
    ( k3_tarski(k1_zfmisc_1(sK5)) != sK5
    | sK5 = k3_tarski(k1_zfmisc_1(sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5945])).

cnf(c_372,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5655,plain,
    ( sK0(sK7,sK6) = sK0(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1524,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
    | X0 != sK0(sK7,sK6)
    | X1 != k3_tarski(k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_5654,plain,
    ( r2_hidden(sK0(sK7,sK6),X0)
    | ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
    | X0 != k3_tarski(k1_zfmisc_1(sK5))
    | sK0(sK7,sK6) != sK0(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_5657,plain,
    ( ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
    | r2_hidden(sK0(sK7,sK6),sK5)
    | sK0(sK7,sK6) != sK0(sK7,sK6)
    | sK5 != k3_tarski(k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5654])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(X0,sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2669,plain,
    ( ~ m1_subset_1(sK0(sK7,sK6),sK5)
    | r2_hidden(sK0(sK7,sK6),sK7)
    | ~ r2_hidden(sK0(sK7,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_746,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_751,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK4(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK4(X1,X2,X0),X1) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X0,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_749,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,X1,X0),sK7) != iProver_top
    | r2_hidden(sK4(sK5,X1,X0),sK6) = iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_750,c_749])).

cnf(c_1845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_1148])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1845,c_25])).

cnf(c_763,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2286,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_763])).

cnf(c_2362,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_2286])).

cnf(c_24,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK4(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_969,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK4(sK5,X0,sK6),sK6)
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK4(sK5,sK7,sK6),sK6)
    | r1_tarski(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_1041,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,sK7,sK6),sK6) != iProver_top
    | r1_tarski(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | m1_subset_1(sK4(sK5,X0,sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1052,plain,
    ( m1_subset_1(sK4(sK5,sK7,sK6),sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | r1_tarski(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_1053,plain,
    ( m1_subset_1(sK4(sK5,sK7,sK6),sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | r2_hidden(sK4(sK5,X0,sK6),X0)
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1185,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | r2_hidden(sK4(sK5,sK7,sK6),sK7)
    | r1_tarski(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1186,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,sK7,sK6),sK7) = iProver_top
    | r1_tarski(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1185])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(sK4(sK5,sK7,sK6),sK5)
    | ~ r2_hidden(sK4(sK5,sK7,sK6),sK7)
    | r2_hidden(sK4(sK5,sK7,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1975,plain,
    ( m1_subset_1(sK4(sK5,sK7,sK6),sK5) != iProver_top
    | r2_hidden(sK4(sK5,sK7,sK6),sK7) != iProver_top
    | r2_hidden(sK4(sK5,sK7,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_2436,plain,
    ( r1_tarski(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_24,c_25,c_1041,c_1053,c_1186,c_1975])).

cnf(c_2438,plain,
    ( r1_tarski(sK7,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2436])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1011,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK5)))
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1206,plain,
    ( r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
    | ~ r2_hidden(sK0(sK7,sK6),sK6)
    | ~ r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1021,plain,
    ( r2_hidden(sK0(sK7,sK6),sK6)
    | ~ r2_xboole_0(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1022,plain,
    ( ~ r2_hidden(sK0(sK7,sK6),sK7)
    | ~ r2_xboole_0(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_949,plain,
    ( ~ r1_tarski(sK7,sK6)
    | r2_xboole_0(sK7,sK6)
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | r2_hidden(sK6,k1_zfmisc_1(sK5))
    | v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_385,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_54,plain,
    ( k3_tarski(k1_zfmisc_1(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_42,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10408,c_5946,c_5655,c_5657,c_2669,c_2438,c_1206,c_1021,c_1022,c_949,c_940,c_385,c_54,c_42,c_19,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.99  
% 2.64/0.99  ------  iProver source info
% 2.64/0.99  
% 2.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.99  git: non_committed_changes: false
% 2.64/0.99  git: last_make_outside_of_git: false
% 2.64/0.99  
% 2.64/0.99  ------ 
% 2.64/0.99  
% 2.64/0.99  ------ Input Options
% 2.64/0.99  
% 2.64/0.99  --out_options                           all
% 2.64/0.99  --tptp_safe_out                         true
% 2.64/0.99  --problem_path                          ""
% 2.64/0.99  --include_path                          ""
% 2.64/0.99  --clausifier                            res/vclausify_rel
% 2.64/0.99  --clausifier_options                    --mode clausify
% 2.64/0.99  --stdin                                 false
% 2.64/0.99  --stats_out                             all
% 2.64/0.99  
% 2.64/0.99  ------ General Options
% 2.64/0.99  
% 2.64/0.99  --fof                                   false
% 2.64/0.99  --time_out_real                         305.
% 2.64/0.99  --time_out_virtual                      -1.
% 2.64/0.99  --symbol_type_check                     false
% 2.64/0.99  --clausify_out                          false
% 2.64/0.99  --sig_cnt_out                           false
% 2.64/1.00  --trig_cnt_out                          false
% 2.64/1.00  --trig_cnt_out_tolerance                1.
% 2.64/1.00  --trig_cnt_out_sk_spl                   false
% 2.64/1.00  --abstr_cl_out                          false
% 2.64/1.00  
% 2.64/1.00  ------ Global Options
% 2.64/1.00  
% 2.64/1.00  --schedule                              default
% 2.64/1.00  --add_important_lit                     false
% 2.64/1.00  --prop_solver_per_cl                    1000
% 2.64/1.00  --min_unsat_core                        false
% 2.64/1.00  --soft_assumptions                      false
% 2.64/1.00  --soft_lemma_size                       3
% 2.64/1.00  --prop_impl_unit_size                   0
% 2.64/1.00  --prop_impl_unit                        []
% 2.64/1.00  --share_sel_clauses                     true
% 2.64/1.00  --reset_solvers                         false
% 2.64/1.00  --bc_imp_inh                            [conj_cone]
% 2.64/1.00  --conj_cone_tolerance                   3.
% 2.64/1.00  --extra_neg_conj                        none
% 2.64/1.00  --large_theory_mode                     true
% 2.64/1.00  --prolific_symb_bound                   200
% 2.64/1.00  --lt_threshold                          2000
% 2.64/1.00  --clause_weak_htbl                      true
% 2.64/1.00  --gc_record_bc_elim                     false
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing Options
% 2.64/1.00  
% 2.64/1.00  --preprocessing_flag                    true
% 2.64/1.00  --time_out_prep_mult                    0.1
% 2.64/1.00  --splitting_mode                        input
% 2.64/1.00  --splitting_grd                         true
% 2.64/1.00  --splitting_cvd                         false
% 2.64/1.00  --splitting_cvd_svl                     false
% 2.64/1.00  --splitting_nvd                         32
% 2.64/1.00  --sub_typing                            true
% 2.64/1.00  --prep_gs_sim                           true
% 2.64/1.00  --prep_unflatten                        true
% 2.64/1.00  --prep_res_sim                          true
% 2.64/1.00  --prep_upred                            true
% 2.64/1.00  --prep_sem_filter                       exhaustive
% 2.64/1.00  --prep_sem_filter_out                   false
% 2.64/1.00  --pred_elim                             true
% 2.64/1.00  --res_sim_input                         true
% 2.64/1.00  --eq_ax_congr_red                       true
% 2.64/1.00  --pure_diseq_elim                       true
% 2.64/1.00  --brand_transform                       false
% 2.64/1.00  --non_eq_to_eq                          false
% 2.64/1.00  --prep_def_merge                        true
% 2.64/1.00  --prep_def_merge_prop_impl              false
% 2.64/1.00  --prep_def_merge_mbd                    true
% 2.64/1.00  --prep_def_merge_tr_red                 false
% 2.64/1.00  --prep_def_merge_tr_cl                  false
% 2.64/1.00  --smt_preprocessing                     true
% 2.64/1.00  --smt_ac_axioms                         fast
% 2.64/1.00  --preprocessed_out                      false
% 2.64/1.00  --preprocessed_stats                    false
% 2.64/1.00  
% 2.64/1.00  ------ Abstraction refinement Options
% 2.64/1.00  
% 2.64/1.00  --abstr_ref                             []
% 2.64/1.00  --abstr_ref_prep                        false
% 2.64/1.00  --abstr_ref_until_sat                   false
% 2.64/1.00  --abstr_ref_sig_restrict                funpre
% 2.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.00  --abstr_ref_under                       []
% 2.64/1.00  
% 2.64/1.00  ------ SAT Options
% 2.64/1.00  
% 2.64/1.00  --sat_mode                              false
% 2.64/1.00  --sat_fm_restart_options                ""
% 2.64/1.00  --sat_gr_def                            false
% 2.64/1.00  --sat_epr_types                         true
% 2.64/1.00  --sat_non_cyclic_types                  false
% 2.64/1.00  --sat_finite_models                     false
% 2.64/1.00  --sat_fm_lemmas                         false
% 2.64/1.00  --sat_fm_prep                           false
% 2.64/1.00  --sat_fm_uc_incr                        true
% 2.64/1.00  --sat_out_model                         small
% 2.64/1.00  --sat_out_clauses                       false
% 2.64/1.00  
% 2.64/1.00  ------ QBF Options
% 2.64/1.00  
% 2.64/1.00  --qbf_mode                              false
% 2.64/1.00  --qbf_elim_univ                         false
% 2.64/1.00  --qbf_dom_inst                          none
% 2.64/1.00  --qbf_dom_pre_inst                      false
% 2.64/1.00  --qbf_sk_in                             false
% 2.64/1.00  --qbf_pred_elim                         true
% 2.64/1.00  --qbf_split                             512
% 2.64/1.00  
% 2.64/1.00  ------ BMC1 Options
% 2.64/1.00  
% 2.64/1.00  --bmc1_incremental                      false
% 2.64/1.00  --bmc1_axioms                           reachable_all
% 2.64/1.00  --bmc1_min_bound                        0
% 2.64/1.00  --bmc1_max_bound                        -1
% 2.64/1.00  --bmc1_max_bound_default                -1
% 2.64/1.00  --bmc1_symbol_reachability              true
% 2.64/1.00  --bmc1_property_lemmas                  false
% 2.64/1.00  --bmc1_k_induction                      false
% 2.64/1.00  --bmc1_non_equiv_states                 false
% 2.64/1.00  --bmc1_deadlock                         false
% 2.64/1.00  --bmc1_ucm                              false
% 2.64/1.00  --bmc1_add_unsat_core                   none
% 2.64/1.00  --bmc1_unsat_core_children              false
% 2.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.00  --bmc1_out_stat                         full
% 2.64/1.00  --bmc1_ground_init                      false
% 2.64/1.00  --bmc1_pre_inst_next_state              false
% 2.64/1.00  --bmc1_pre_inst_state                   false
% 2.64/1.00  --bmc1_pre_inst_reach_state             false
% 2.64/1.00  --bmc1_out_unsat_core                   false
% 2.64/1.00  --bmc1_aig_witness_out                  false
% 2.64/1.00  --bmc1_verbose                          false
% 2.64/1.00  --bmc1_dump_clauses_tptp                false
% 2.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.00  --bmc1_dump_file                        -
% 2.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.00  --bmc1_ucm_extend_mode                  1
% 2.64/1.00  --bmc1_ucm_init_mode                    2
% 2.64/1.00  --bmc1_ucm_cone_mode                    none
% 2.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.00  --bmc1_ucm_relax_model                  4
% 2.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.00  --bmc1_ucm_layered_model                none
% 2.64/1.00  --bmc1_ucm_max_lemma_size               10
% 2.64/1.00  
% 2.64/1.00  ------ AIG Options
% 2.64/1.00  
% 2.64/1.00  --aig_mode                              false
% 2.64/1.00  
% 2.64/1.00  ------ Instantiation Options
% 2.64/1.00  
% 2.64/1.00  --instantiation_flag                    true
% 2.64/1.00  --inst_sos_flag                         false
% 2.64/1.00  --inst_sos_phase                        true
% 2.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.00  --inst_lit_sel_side                     num_symb
% 2.64/1.00  --inst_solver_per_active                1400
% 2.64/1.00  --inst_solver_calls_frac                1.
% 2.64/1.00  --inst_passive_queue_type               priority_queues
% 2.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.00  --inst_passive_queues_freq              [25;2]
% 2.64/1.00  --inst_dismatching                      true
% 2.64/1.00  --inst_eager_unprocessed_to_passive     true
% 2.64/1.00  --inst_prop_sim_given                   true
% 2.64/1.00  --inst_prop_sim_new                     false
% 2.64/1.00  --inst_subs_new                         false
% 2.64/1.00  --inst_eq_res_simp                      false
% 2.64/1.00  --inst_subs_given                       false
% 2.64/1.00  --inst_orphan_elimination               true
% 2.64/1.00  --inst_learning_loop_flag               true
% 2.64/1.00  --inst_learning_start                   3000
% 2.64/1.00  --inst_learning_factor                  2
% 2.64/1.00  --inst_start_prop_sim_after_learn       3
% 2.64/1.00  --inst_sel_renew                        solver
% 2.64/1.00  --inst_lit_activity_flag                true
% 2.64/1.00  --inst_restr_to_given                   false
% 2.64/1.00  --inst_activity_threshold               500
% 2.64/1.00  --inst_out_proof                        true
% 2.64/1.00  
% 2.64/1.00  ------ Resolution Options
% 2.64/1.00  
% 2.64/1.00  --resolution_flag                       true
% 2.64/1.00  --res_lit_sel                           adaptive
% 2.64/1.00  --res_lit_sel_side                      none
% 2.64/1.00  --res_ordering                          kbo
% 2.64/1.00  --res_to_prop_solver                    active
% 2.64/1.00  --res_prop_simpl_new                    false
% 2.64/1.00  --res_prop_simpl_given                  true
% 2.64/1.00  --res_passive_queue_type                priority_queues
% 2.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.00  --res_passive_queues_freq               [15;5]
% 2.64/1.00  --res_forward_subs                      full
% 2.64/1.00  --res_backward_subs                     full
% 2.64/1.00  --res_forward_subs_resolution           true
% 2.64/1.00  --res_backward_subs_resolution          true
% 2.64/1.00  --res_orphan_elimination                true
% 2.64/1.00  --res_time_limit                        2.
% 2.64/1.00  --res_out_proof                         true
% 2.64/1.00  
% 2.64/1.00  ------ Superposition Options
% 2.64/1.00  
% 2.64/1.00  --superposition_flag                    true
% 2.64/1.00  --sup_passive_queue_type                priority_queues
% 2.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.00  --demod_completeness_check              fast
% 2.64/1.00  --demod_use_ground                      true
% 2.64/1.00  --sup_to_prop_solver                    passive
% 2.64/1.00  --sup_prop_simpl_new                    true
% 2.64/1.00  --sup_prop_simpl_given                  true
% 2.64/1.00  --sup_fun_splitting                     false
% 2.64/1.00  --sup_smt_interval                      50000
% 2.64/1.00  
% 2.64/1.00  ------ Superposition Simplification Setup
% 2.64/1.00  
% 2.64/1.00  --sup_indices_passive                   []
% 2.64/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_full_bw                           [BwDemod]
% 2.64/1.00  --sup_immed_triv                        [TrivRules]
% 2.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_immed_bw_main                     []
% 2.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.00  
% 2.64/1.00  ------ Combination Options
% 2.64/1.00  
% 2.64/1.00  --comb_res_mult                         3
% 2.64/1.00  --comb_sup_mult                         2
% 2.64/1.00  --comb_inst_mult                        10
% 2.64/1.00  
% 2.64/1.00  ------ Debug Options
% 2.64/1.00  
% 2.64/1.00  --dbg_backtrace                         false
% 2.64/1.00  --dbg_dump_prop_clauses                 false
% 2.64/1.00  --dbg_dump_prop_clauses_file            -
% 2.64/1.00  --dbg_out_stat                          false
% 2.64/1.00  ------ Parsing...
% 2.64/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/1.00  ------ Proving...
% 2.64/1.00  ------ Problem Properties 
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  clauses                                 24
% 2.64/1.00  conjectures                             5
% 2.64/1.00  EPR                                     9
% 2.64/1.00  Horn                                    18
% 2.64/1.00  unary                                   5
% 2.64/1.00  binary                                  6
% 2.64/1.00  lits                                    60
% 2.64/1.00  lits eq                                 6
% 2.64/1.00  fd_pure                                 0
% 2.64/1.00  fd_pseudo                               0
% 2.64/1.00  fd_cond                                 0
% 2.64/1.00  fd_pseudo_cond                          4
% 2.64/1.00  AC symbols                              0
% 2.64/1.00  
% 2.64/1.00  ------ Schedule dynamic 5 is on 
% 2.64/1.00  
% 2.64/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  ------ 
% 2.64/1.00  Current options:
% 2.64/1.00  ------ 
% 2.64/1.00  
% 2.64/1.00  ------ Input Options
% 2.64/1.00  
% 2.64/1.00  --out_options                           all
% 2.64/1.00  --tptp_safe_out                         true
% 2.64/1.00  --problem_path                          ""
% 2.64/1.00  --include_path                          ""
% 2.64/1.00  --clausifier                            res/vclausify_rel
% 2.64/1.00  --clausifier_options                    --mode clausify
% 2.64/1.00  --stdin                                 false
% 2.64/1.00  --stats_out                             all
% 2.64/1.00  
% 2.64/1.00  ------ General Options
% 2.64/1.00  
% 2.64/1.00  --fof                                   false
% 2.64/1.00  --time_out_real                         305.
% 2.64/1.00  --time_out_virtual                      -1.
% 2.64/1.00  --symbol_type_check                     false
% 2.64/1.00  --clausify_out                          false
% 2.64/1.00  --sig_cnt_out                           false
% 2.64/1.00  --trig_cnt_out                          false
% 2.64/1.00  --trig_cnt_out_tolerance                1.
% 2.64/1.00  --trig_cnt_out_sk_spl                   false
% 2.64/1.00  --abstr_cl_out                          false
% 2.64/1.00  
% 2.64/1.00  ------ Global Options
% 2.64/1.00  
% 2.64/1.00  --schedule                              default
% 2.64/1.00  --add_important_lit                     false
% 2.64/1.00  --prop_solver_per_cl                    1000
% 2.64/1.00  --min_unsat_core                        false
% 2.64/1.00  --soft_assumptions                      false
% 2.64/1.00  --soft_lemma_size                       3
% 2.64/1.00  --prop_impl_unit_size                   0
% 2.64/1.00  --prop_impl_unit                        []
% 2.64/1.00  --share_sel_clauses                     true
% 2.64/1.00  --reset_solvers                         false
% 2.64/1.00  --bc_imp_inh                            [conj_cone]
% 2.64/1.00  --conj_cone_tolerance                   3.
% 2.64/1.00  --extra_neg_conj                        none
% 2.64/1.00  --large_theory_mode                     true
% 2.64/1.00  --prolific_symb_bound                   200
% 2.64/1.00  --lt_threshold                          2000
% 2.64/1.00  --clause_weak_htbl                      true
% 2.64/1.00  --gc_record_bc_elim                     false
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing Options
% 2.64/1.00  
% 2.64/1.00  --preprocessing_flag                    true
% 2.64/1.00  --time_out_prep_mult                    0.1
% 2.64/1.00  --splitting_mode                        input
% 2.64/1.00  --splitting_grd                         true
% 2.64/1.00  --splitting_cvd                         false
% 2.64/1.00  --splitting_cvd_svl                     false
% 2.64/1.00  --splitting_nvd                         32
% 2.64/1.00  --sub_typing                            true
% 2.64/1.00  --prep_gs_sim                           true
% 2.64/1.00  --prep_unflatten                        true
% 2.64/1.00  --prep_res_sim                          true
% 2.64/1.00  --prep_upred                            true
% 2.64/1.00  --prep_sem_filter                       exhaustive
% 2.64/1.00  --prep_sem_filter_out                   false
% 2.64/1.00  --pred_elim                             true
% 2.64/1.00  --res_sim_input                         true
% 2.64/1.00  --eq_ax_congr_red                       true
% 2.64/1.00  --pure_diseq_elim                       true
% 2.64/1.00  --brand_transform                       false
% 2.64/1.00  --non_eq_to_eq                          false
% 2.64/1.00  --prep_def_merge                        true
% 2.64/1.00  --prep_def_merge_prop_impl              false
% 2.64/1.00  --prep_def_merge_mbd                    true
% 2.64/1.00  --prep_def_merge_tr_red                 false
% 2.64/1.00  --prep_def_merge_tr_cl                  false
% 2.64/1.00  --smt_preprocessing                     true
% 2.64/1.00  --smt_ac_axioms                         fast
% 2.64/1.00  --preprocessed_out                      false
% 2.64/1.00  --preprocessed_stats                    false
% 2.64/1.00  
% 2.64/1.00  ------ Abstraction refinement Options
% 2.64/1.00  
% 2.64/1.00  --abstr_ref                             []
% 2.64/1.00  --abstr_ref_prep                        false
% 2.64/1.00  --abstr_ref_until_sat                   false
% 2.64/1.00  --abstr_ref_sig_restrict                funpre
% 2.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.00  --abstr_ref_under                       []
% 2.64/1.00  
% 2.64/1.00  ------ SAT Options
% 2.64/1.00  
% 2.64/1.00  --sat_mode                              false
% 2.64/1.00  --sat_fm_restart_options                ""
% 2.64/1.00  --sat_gr_def                            false
% 2.64/1.00  --sat_epr_types                         true
% 2.64/1.00  --sat_non_cyclic_types                  false
% 2.64/1.00  --sat_finite_models                     false
% 2.64/1.00  --sat_fm_lemmas                         false
% 2.64/1.00  --sat_fm_prep                           false
% 2.64/1.00  --sat_fm_uc_incr                        true
% 2.64/1.00  --sat_out_model                         small
% 2.64/1.00  --sat_out_clauses                       false
% 2.64/1.00  
% 2.64/1.00  ------ QBF Options
% 2.64/1.00  
% 2.64/1.00  --qbf_mode                              false
% 2.64/1.00  --qbf_elim_univ                         false
% 2.64/1.00  --qbf_dom_inst                          none
% 2.64/1.00  --qbf_dom_pre_inst                      false
% 2.64/1.00  --qbf_sk_in                             false
% 2.64/1.00  --qbf_pred_elim                         true
% 2.64/1.00  --qbf_split                             512
% 2.64/1.00  
% 2.64/1.00  ------ BMC1 Options
% 2.64/1.00  
% 2.64/1.00  --bmc1_incremental                      false
% 2.64/1.00  --bmc1_axioms                           reachable_all
% 2.64/1.00  --bmc1_min_bound                        0
% 2.64/1.00  --bmc1_max_bound                        -1
% 2.64/1.00  --bmc1_max_bound_default                -1
% 2.64/1.00  --bmc1_symbol_reachability              true
% 2.64/1.00  --bmc1_property_lemmas                  false
% 2.64/1.00  --bmc1_k_induction                      false
% 2.64/1.00  --bmc1_non_equiv_states                 false
% 2.64/1.00  --bmc1_deadlock                         false
% 2.64/1.00  --bmc1_ucm                              false
% 2.64/1.00  --bmc1_add_unsat_core                   none
% 2.64/1.00  --bmc1_unsat_core_children              false
% 2.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.00  --bmc1_out_stat                         full
% 2.64/1.00  --bmc1_ground_init                      false
% 2.64/1.00  --bmc1_pre_inst_next_state              false
% 2.64/1.00  --bmc1_pre_inst_state                   false
% 2.64/1.00  --bmc1_pre_inst_reach_state             false
% 2.64/1.00  --bmc1_out_unsat_core                   false
% 2.64/1.00  --bmc1_aig_witness_out                  false
% 2.64/1.00  --bmc1_verbose                          false
% 2.64/1.00  --bmc1_dump_clauses_tptp                false
% 2.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.00  --bmc1_dump_file                        -
% 2.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.00  --bmc1_ucm_extend_mode                  1
% 2.64/1.00  --bmc1_ucm_init_mode                    2
% 2.64/1.00  --bmc1_ucm_cone_mode                    none
% 2.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.00  --bmc1_ucm_relax_model                  4
% 2.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.00  --bmc1_ucm_layered_model                none
% 2.64/1.00  --bmc1_ucm_max_lemma_size               10
% 2.64/1.00  
% 2.64/1.00  ------ AIG Options
% 2.64/1.00  
% 2.64/1.00  --aig_mode                              false
% 2.64/1.00  
% 2.64/1.00  ------ Instantiation Options
% 2.64/1.00  
% 2.64/1.00  --instantiation_flag                    true
% 2.64/1.00  --inst_sos_flag                         false
% 2.64/1.00  --inst_sos_phase                        true
% 2.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.00  --inst_lit_sel_side                     none
% 2.64/1.00  --inst_solver_per_active                1400
% 2.64/1.00  --inst_solver_calls_frac                1.
% 2.64/1.00  --inst_passive_queue_type               priority_queues
% 2.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.00  --inst_passive_queues_freq              [25;2]
% 2.64/1.00  --inst_dismatching                      true
% 2.64/1.00  --inst_eager_unprocessed_to_passive     true
% 2.64/1.00  --inst_prop_sim_given                   true
% 2.64/1.00  --inst_prop_sim_new                     false
% 2.64/1.00  --inst_subs_new                         false
% 2.64/1.00  --inst_eq_res_simp                      false
% 2.64/1.00  --inst_subs_given                       false
% 2.64/1.00  --inst_orphan_elimination               true
% 2.64/1.00  --inst_learning_loop_flag               true
% 2.64/1.00  --inst_learning_start                   3000
% 2.64/1.00  --inst_learning_factor                  2
% 2.64/1.00  --inst_start_prop_sim_after_learn       3
% 2.64/1.00  --inst_sel_renew                        solver
% 2.64/1.00  --inst_lit_activity_flag                true
% 2.64/1.00  --inst_restr_to_given                   false
% 2.64/1.00  --inst_activity_threshold               500
% 2.64/1.00  --inst_out_proof                        true
% 2.64/1.00  
% 2.64/1.00  ------ Resolution Options
% 2.64/1.00  
% 2.64/1.00  --resolution_flag                       false
% 2.64/1.00  --res_lit_sel                           adaptive
% 2.64/1.00  --res_lit_sel_side                      none
% 2.64/1.00  --res_ordering                          kbo
% 2.64/1.00  --res_to_prop_solver                    active
% 2.64/1.00  --res_prop_simpl_new                    false
% 2.64/1.00  --res_prop_simpl_given                  true
% 2.64/1.00  --res_passive_queue_type                priority_queues
% 2.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.00  --res_passive_queues_freq               [15;5]
% 2.64/1.00  --res_forward_subs                      full
% 2.64/1.00  --res_backward_subs                     full
% 2.64/1.00  --res_forward_subs_resolution           true
% 2.64/1.00  --res_backward_subs_resolution          true
% 2.64/1.00  --res_orphan_elimination                true
% 2.64/1.00  --res_time_limit                        2.
% 2.64/1.00  --res_out_proof                         true
% 2.64/1.00  
% 2.64/1.00  ------ Superposition Options
% 2.64/1.00  
% 2.64/1.00  --superposition_flag                    true
% 2.64/1.00  --sup_passive_queue_type                priority_queues
% 2.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.00  --demod_completeness_check              fast
% 2.64/1.00  --demod_use_ground                      true
% 2.64/1.00  --sup_to_prop_solver                    passive
% 2.64/1.00  --sup_prop_simpl_new                    true
% 2.64/1.00  --sup_prop_simpl_given                  true
% 2.64/1.00  --sup_fun_splitting                     false
% 2.64/1.00  --sup_smt_interval                      50000
% 2.64/1.00  
% 2.64/1.00  ------ Superposition Simplification Setup
% 2.64/1.00  
% 2.64/1.00  --sup_indices_passive                   []
% 2.64/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_full_bw                           [BwDemod]
% 2.64/1.00  --sup_immed_triv                        [TrivRules]
% 2.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_immed_bw_main                     []
% 2.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.00  
% 2.64/1.00  ------ Combination Options
% 2.64/1.00  
% 2.64/1.00  --comb_res_mult                         3
% 2.64/1.00  --comb_sup_mult                         2
% 2.64/1.00  --comb_inst_mult                        10
% 2.64/1.00  
% 2.64/1.00  ------ Debug Options
% 2.64/1.00  
% 2.64/1.00  --dbg_backtrace                         false
% 2.64/1.00  --dbg_dump_prop_clauses                 false
% 2.64/1.00  --dbg_dump_prop_clauses_file            -
% 2.64/1.00  --dbg_out_stat                          false
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  ------ Proving...
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  % SZS status Theorem for theBenchmark.p
% 2.64/1.00  
% 2.64/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/1.00  
% 2.64/1.00  fof(f6,axiom,(
% 2.64/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f16,plain,(
% 2.64/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.64/1.00    inference(ennf_transformation,[],[f6])).
% 2.64/1.00  
% 2.64/1.00  fof(f29,plain,(
% 2.64/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.64/1.00    inference(nnf_transformation,[],[f16])).
% 2.64/1.00  
% 2.64/1.00  fof(f48,plain,(
% 2.64/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f29])).
% 2.64/1.00  
% 2.64/1.00  fof(f3,axiom,(
% 2.64/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f15,plain,(
% 2.64/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.64/1.00    inference(ennf_transformation,[],[f3])).
% 2.64/1.00  
% 2.64/1.00  fof(f39,plain,(
% 2.64/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f15])).
% 2.64/1.00  
% 2.64/1.00  fof(f9,conjecture,(
% 2.64/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f10,negated_conjecture,(
% 2.64/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 2.64/1.00    inference(negated_conjecture,[],[f9])).
% 2.64/1.00  
% 2.64/1.00  fof(f19,plain,(
% 2.64/1.00    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(ennf_transformation,[],[f10])).
% 2.64/1.00  
% 2.64/1.00  fof(f20,plain,(
% 2.64/1.00    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(flattening,[],[f19])).
% 2.64/1.00  
% 2.64/1.00  fof(f32,plain,(
% 2.64/1.00    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(nnf_transformation,[],[f20])).
% 2.64/1.00  
% 2.64/1.00  fof(f34,plain,(
% 2.64/1.00    ( ! [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (sK7 != X1 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,sK7)) & (r2_hidden(X3,sK7) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK7,k1_zfmisc_1(X0)))) )),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f33,plain,(
% 2.64/1.00    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK6 != X2 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,sK5)) & m1_subset_1(X2,k1_zfmisc_1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(sK5)))),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f35,plain,(
% 2.64/1.00    (sK6 != sK7 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(X3,sK7)) & (r2_hidden(X3,sK7) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 2.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f34,f33])).
% 2.64/1.00  
% 2.64/1.00  fof(f57,plain,(
% 2.64/1.00    ( ! [X3] : (r2_hidden(X3,sK7) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,sK5)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f35])).
% 2.64/1.00  
% 2.64/1.00  fof(f55,plain,(
% 2.64/1.00    m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 2.64/1.00    inference(cnf_transformation,[],[f35])).
% 2.64/1.00  
% 2.64/1.00  fof(f8,axiom,(
% 2.64/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f17,plain,(
% 2.64/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(ennf_transformation,[],[f8])).
% 2.64/1.00  
% 2.64/1.00  fof(f18,plain,(
% 2.64/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(flattening,[],[f17])).
% 2.64/1.00  
% 2.64/1.00  fof(f30,plain,(
% 2.64/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f31,plain,(
% 2.64/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).
% 2.64/1.00  
% 2.64/1.00  fof(f53,plain,(
% 2.64/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.64/1.00    inference(cnf_transformation,[],[f31])).
% 2.64/1.00  
% 2.64/1.00  fof(f52,plain,(
% 2.64/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.64/1.00    inference(cnf_transformation,[],[f31])).
% 2.64/1.00  
% 2.64/1.00  fof(f58,plain,(
% 2.64/1.00    ( ! [X3] : (r2_hidden(X3,sK6) | ~r2_hidden(X3,sK7) | ~m1_subset_1(X3,sK5)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f35])).
% 2.64/1.00  
% 2.64/1.00  fof(f56,plain,(
% 2.64/1.00    m1_subset_1(sK7,k1_zfmisc_1(sK5))),
% 2.64/1.00    inference(cnf_transformation,[],[f35])).
% 2.64/1.00  
% 2.64/1.00  fof(f54,plain,(
% 2.64/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.64/1.00    inference(cnf_transformation,[],[f31])).
% 2.64/1.00  
% 2.64/1.00  fof(f4,axiom,(
% 2.64/1.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f23,plain,(
% 2.64/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.64/1.00    inference(nnf_transformation,[],[f4])).
% 2.64/1.00  
% 2.64/1.00  fof(f24,plain,(
% 2.64/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.64/1.00    inference(rectify,[],[f23])).
% 2.64/1.00  
% 2.64/1.00  fof(f27,plain,(
% 2.64/1.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f26,plain,(
% 2.64/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f25,plain,(
% 2.64/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f28,plain,(
% 2.64/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).
% 2.64/1.00  
% 2.64/1.00  fof(f42,plain,(
% 2.64/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 2.64/1.00    inference(cnf_transformation,[],[f28])).
% 2.64/1.00  
% 2.64/1.00  fof(f60,plain,(
% 2.64/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 2.64/1.00    inference(equality_resolution,[],[f42])).
% 2.64/1.00  
% 2.64/1.00  fof(f2,axiom,(
% 2.64/1.00    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f14,plain,(
% 2.64/1.00    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 2.64/1.00    inference(ennf_transformation,[],[f2])).
% 2.64/1.00  
% 2.64/1.00  fof(f21,plain,(
% 2.64/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1)))),
% 2.64/1.00    introduced(choice_axiom,[])).
% 2.64/1.00  
% 2.64/1.00  fof(f22,plain,(
% 2.64/1.00    ! [X0,X1] : ((~r2_hidden(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 2.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 2.64/1.00  
% 2.64/1.00  fof(f37,plain,(
% 2.64/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f22])).
% 2.64/1.00  
% 2.64/1.00  fof(f38,plain,(
% 2.64/1.00    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f22])).
% 2.64/1.00  
% 2.64/1.00  fof(f1,axiom,(
% 2.64/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f11,plain,(
% 2.64/1.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.64/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.64/1.00  
% 2.64/1.00  fof(f12,plain,(
% 2.64/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.64/1.00    inference(ennf_transformation,[],[f11])).
% 2.64/1.00  
% 2.64/1.00  fof(f13,plain,(
% 2.64/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.64/1.00    inference(flattening,[],[f12])).
% 2.64/1.00  
% 2.64/1.00  fof(f36,plain,(
% 2.64/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f13])).
% 2.64/1.00  
% 2.64/1.00  fof(f47,plain,(
% 2.64/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.64/1.00    inference(cnf_transformation,[],[f29])).
% 2.64/1.00  
% 2.64/1.00  fof(f5,axiom,(
% 2.64/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f46,plain,(
% 2.64/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.64/1.00    inference(cnf_transformation,[],[f5])).
% 2.64/1.00  
% 2.64/1.00  fof(f7,axiom,(
% 2.64/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.00  
% 2.64/1.00  fof(f51,plain,(
% 2.64/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.64/1.00    inference(cnf_transformation,[],[f7])).
% 2.64/1.00  
% 2.64/1.00  fof(f59,plain,(
% 2.64/1.00    sK6 != sK7),
% 2.64/1.00    inference(cnf_transformation,[],[f35])).
% 2.64/1.00  
% 2.64/1.00  cnf(c_13,plain,
% 2.64/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.64/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_3,plain,
% 2.64/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.64/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_139,plain,
% 2.64/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.64/1.00      inference(global_propositional_subsumption,
% 2.64/1.00                [status(thm)],
% 2.64/1.00                [c_13,c_3]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_140,plain,
% 2.64/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.64/1.00      inference(renaming,[status(thm)],[c_139]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_10406,plain,
% 2.64/1.00      ( m1_subset_1(sK0(sK7,sK6),X0) | ~ r2_hidden(sK0(sK7,sK6),X0) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_10408,plain,
% 2.64/1.00      ( m1_subset_1(sK0(sK7,sK6),sK5) | ~ r2_hidden(sK0(sK7,sK6),sK5) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_10406]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_373,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_5945,plain,
% 2.64/1.00      ( X0 != X1
% 2.64/1.00      | X0 = k3_tarski(k1_zfmisc_1(sK5))
% 2.64/1.00      | k3_tarski(k1_zfmisc_1(sK5)) != X1 ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_373]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_5946,plain,
% 2.64/1.00      ( k3_tarski(k1_zfmisc_1(sK5)) != sK5
% 2.64/1.00      | sK5 = k3_tarski(k1_zfmisc_1(sK5))
% 2.64/1.00      | sK5 != sK5 ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_5945]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_372,plain,( X0 = X0 ),theory(equality) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_5655,plain,
% 2.64/1.00      ( sK0(sK7,sK6) = sK0(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_372]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_374,plain,
% 2.64/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.64/1.00      theory(equality) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1524,plain,
% 2.64/1.00      ( r2_hidden(X0,X1)
% 2.64/1.00      | ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
% 2.64/1.00      | X0 != sK0(sK7,sK6)
% 2.64/1.00      | X1 != k3_tarski(k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_374]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_5654,plain,
% 2.64/1.00      ( r2_hidden(sK0(sK7,sK6),X0)
% 2.64/1.00      | ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
% 2.64/1.00      | X0 != k3_tarski(k1_zfmisc_1(sK5))
% 2.64/1.00      | sK0(sK7,sK6) != sK0(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_1524]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_5657,plain,
% 2.64/1.00      ( ~ r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
% 2.64/1.00      | r2_hidden(sK0(sK7,sK6),sK5)
% 2.64/1.00      | sK0(sK7,sK6) != sK0(sK7,sK6)
% 2.64/1.00      | sK5 != k3_tarski(k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_5654]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_21,negated_conjecture,
% 2.64/1.00      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK7) | ~ r2_hidden(X0,sK6) ),
% 2.64/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2669,plain,
% 2.64/1.00      ( ~ m1_subset_1(sK0(sK7,sK6),sK5)
% 2.64/1.00      | r2_hidden(sK0(sK7,sK6),sK7)
% 2.64/1.00      | ~ r2_hidden(sK0(sK7,sK6),sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_23,negated_conjecture,
% 2.64/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_746,plain,
% 2.64/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_17,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.64/1.00      | r2_hidden(sK4(X1,X2,X0),X2)
% 2.64/1.00      | r1_tarski(X2,X0) ),
% 2.64/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_751,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.64/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
% 2.64/1.00      | r1_tarski(X2,X0) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_18,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.64/1.00      | m1_subset_1(sK4(X1,X2,X0),X1)
% 2.64/1.00      | r1_tarski(X2,X0) ),
% 2.64/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_750,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.64/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.64/1.00      | m1_subset_1(sK4(X1,X2,X0),X1) = iProver_top
% 2.64/1.00      | r1_tarski(X2,X0) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_20,negated_conjecture,
% 2.64/1.00      ( ~ m1_subset_1(X0,sK5) | ~ r2_hidden(X0,sK7) | r2_hidden(X0,sK6) ),
% 2.64/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_749,plain,
% 2.64/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 2.64/1.00      | r2_hidden(X0,sK7) != iProver_top
% 2.64/1.00      | r2_hidden(X0,sK6) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1148,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,X1,X0),sK7) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,X1,X0),sK6) = iProver_top
% 2.64/1.00      | r1_tarski(X1,X0) = iProver_top ),
% 2.64/1.00      inference(superposition,[status(thm)],[c_750,c_749]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1845,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,X0),sK6) = iProver_top
% 2.64/1.00      | r1_tarski(sK7,X0) = iProver_top ),
% 2.64/1.00      inference(superposition,[status(thm)],[c_751,c_1148]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_22,negated_conjecture,
% 2.64/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_25,plain,
% 2.64/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2277,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,X0),sK6) = iProver_top
% 2.64/1.00      | r1_tarski(sK7,X0) = iProver_top ),
% 2.64/1.00      inference(global_propositional_subsumption,
% 2.64/1.00                [status(thm)],
% 2.64/1.00                [c_1845,c_25]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_763,plain,
% 2.64/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.64/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2286,plain,
% 2.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r1_tarski(sK7,X0) = iProver_top
% 2.64/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.64/1.00      inference(superposition,[status(thm)],[c_2277,c_763]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2362,plain,
% 2.64/1.00      ( r1_tarski(sK7,sK6) = iProver_top
% 2.64/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.64/1.00      inference(superposition,[status(thm)],[c_746,c_2286]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_24,plain,
% 2.64/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_16,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.64/1.00      | ~ r2_hidden(sK4(X1,X2,X0),X0)
% 2.64/1.00      | r1_tarski(X2,X0) ),
% 2.64/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_969,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ r2_hidden(sK4(sK5,X0,sK6),sK6)
% 2.64/1.00      | r1_tarski(X0,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1040,plain,
% 2.64/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ r2_hidden(sK4(sK5,sK7,sK6),sK6)
% 2.64/1.00      | r1_tarski(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_969]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1041,plain,
% 2.64/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK6) != iProver_top
% 2.64/1.00      | r1_tarski(sK7,sK6) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_994,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
% 2.64/1.00      | m1_subset_1(sK4(sK5,X0,sK6),sK5)
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | r1_tarski(X0,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1052,plain,
% 2.64/1.00      ( m1_subset_1(sK4(sK5,sK7,sK6),sK5)
% 2.64/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | r1_tarski(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_994]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1053,plain,
% 2.64/1.00      ( m1_subset_1(sK4(sK5,sK7,sK6),sK5) = iProver_top
% 2.64/1.00      | m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r1_tarski(sK7,sK6) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_979,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | r2_hidden(sK4(sK5,X0,sK6),X0)
% 2.64/1.00      | r1_tarski(X0,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1185,plain,
% 2.64/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
% 2.64/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK7)
% 2.64/1.00      | r1_tarski(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_979]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1186,plain,
% 2.64/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | m1_subset_1(sK6,k1_zfmisc_1(sK5)) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK7) = iProver_top
% 2.64/1.00      | r1_tarski(sK7,sK6) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_1185]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1974,plain,
% 2.64/1.00      ( ~ m1_subset_1(sK4(sK5,sK7,sK6),sK5)
% 2.64/1.00      | ~ r2_hidden(sK4(sK5,sK7,sK6),sK7)
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1975,plain,
% 2.64/1.00      ( m1_subset_1(sK4(sK5,sK7,sK6),sK5) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK7) != iProver_top
% 2.64/1.00      | r2_hidden(sK4(sK5,sK7,sK6),sK6) = iProver_top ),
% 2.64/1.00      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2436,plain,
% 2.64/1.00      ( r1_tarski(sK7,sK6) = iProver_top ),
% 2.64/1.00      inference(global_propositional_subsumption,
% 2.64/1.00                [status(thm)],
% 2.64/1.00                [c_2362,c_24,c_25,c_1041,c_1053,c_1186,c_1975]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2438,plain,
% 2.64/1.00      ( r1_tarski(sK7,sK6) ),
% 2.64/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2436]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_7,plain,
% 2.64/1.00      ( ~ r2_hidden(X0,X1)
% 2.64/1.00      | ~ r2_hidden(X2,X0)
% 2.64/1.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 2.64/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1011,plain,
% 2.64/1.00      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK5)))
% 2.64/1.00      | ~ r2_hidden(X0,sK6)
% 2.64/1.00      | ~ r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1206,plain,
% 2.64/1.00      ( r2_hidden(sK0(sK7,sK6),k3_tarski(k1_zfmisc_1(sK5)))
% 2.64/1.00      | ~ r2_hidden(sK0(sK7,sK6),sK6)
% 2.64/1.00      | ~ r2_hidden(sK6,k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_2,plain,
% 2.64/1.00      ( r2_hidden(sK0(X0,X1),X1) | ~ r2_xboole_0(X0,X1) ),
% 2.64/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1021,plain,
% 2.64/1.00      ( r2_hidden(sK0(sK7,sK6),sK6) | ~ r2_xboole_0(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1,plain,
% 2.64/1.00      ( ~ r2_hidden(sK0(X0,X1),X0) | ~ r2_xboole_0(X0,X1) ),
% 2.64/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_1022,plain,
% 2.64/1.00      ( ~ r2_hidden(sK0(sK7,sK6),sK7) | ~ r2_xboole_0(sK7,sK6) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_0,plain,
% 2.64/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.64/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_949,plain,
% 2.64/1.00      ( ~ r1_tarski(sK7,sK6) | r2_xboole_0(sK7,sK6) | sK6 = sK7 ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_14,plain,
% 2.64/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.64/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_940,plain,
% 2.64/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | r2_hidden(sK6,k1_zfmisc_1(sK5))
% 2.64/1.00      | v1_xboole_0(k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_385,plain,
% 2.64/1.00      ( sK5 = sK5 ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_372]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_10,plain,
% 2.64/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.64/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_54,plain,
% 2.64/1.00      ( k3_tarski(k1_zfmisc_1(sK5)) = sK5 ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_15,plain,
% 2.64/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.64/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_42,plain,
% 2.64/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(sK5)) ),
% 2.64/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(c_19,negated_conjecture,
% 2.64/1.00      ( sK6 != sK7 ),
% 2.64/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.64/1.00  
% 2.64/1.00  cnf(contradiction,plain,
% 2.64/1.00      ( $false ),
% 2.64/1.00      inference(minisat,
% 2.64/1.00                [status(thm)],
% 2.64/1.00                [c_10408,c_5946,c_5655,c_5657,c_2669,c_2438,c_1206,
% 2.64/1.00                 c_1021,c_1022,c_949,c_940,c_385,c_54,c_42,c_19,c_23]) ).
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/1.00  
% 2.64/1.00  ------                               Statistics
% 2.64/1.00  
% 2.64/1.00  ------ General
% 2.64/1.00  
% 2.64/1.00  abstr_ref_over_cycles:                  0
% 2.64/1.00  abstr_ref_under_cycles:                 0
% 2.64/1.00  gc_basic_clause_elim:                   0
% 2.64/1.00  forced_gc_time:                         0
% 2.64/1.00  parsing_time:                           0.008
% 2.64/1.00  unif_index_cands_time:                  0.
% 2.64/1.00  unif_index_add_time:                    0.
% 2.64/1.00  orderings_time:                         0.
% 2.64/1.00  out_proof_time:                         0.009
% 2.64/1.00  total_time:                             0.275
% 2.64/1.00  num_of_symbols:                         46
% 2.64/1.00  num_of_terms:                           9773
% 2.64/1.00  
% 2.64/1.00  ------ Preprocessing
% 2.64/1.00  
% 2.64/1.00  num_of_splits:                          0
% 2.64/1.00  num_of_split_atoms:                     0
% 2.64/1.00  num_of_reused_defs:                     0
% 2.64/1.00  num_eq_ax_congr_red:                    30
% 2.64/1.00  num_of_sem_filtered_clauses:            1
% 2.64/1.00  num_of_subtypes:                        0
% 2.64/1.00  monotx_restored_types:                  0
% 2.64/1.00  sat_num_of_epr_types:                   0
% 2.64/1.00  sat_num_of_non_cyclic_types:            0
% 2.64/1.00  sat_guarded_non_collapsed_types:        0
% 2.64/1.00  num_pure_diseq_elim:                    0
% 2.64/1.00  simp_replaced_by:                       0
% 2.64/1.00  res_preprocessed:                       87
% 2.64/1.00  prep_upred:                             0
% 2.64/1.00  prep_unflattend:                        6
% 2.64/1.00  smt_new_axioms:                         0
% 2.64/1.00  pred_elim_cands:                        5
% 2.64/1.00  pred_elim:                              0
% 2.64/1.00  pred_elim_cl:                           0
% 2.64/1.00  pred_elim_cycles:                       2
% 2.64/1.00  merged_defs:                            0
% 2.64/1.00  merged_defs_ncl:                        0
% 2.64/1.00  bin_hyper_res:                          0
% 2.64/1.00  prep_cycles:                            3
% 2.64/1.00  pred_elim_time:                         0.001
% 2.64/1.00  splitting_time:                         0.
% 2.64/1.00  sem_filter_time:                        0.
% 2.64/1.00  monotx_time:                            0.
% 2.64/1.00  subtype_inf_time:                       0.
% 2.64/1.00  
% 2.64/1.00  ------ Problem properties
% 2.64/1.00  
% 2.64/1.00  clauses:                                24
% 2.64/1.00  conjectures:                            5
% 2.64/1.00  epr:                                    9
% 2.64/1.00  horn:                                   18
% 2.64/1.00  ground:                                 3
% 2.64/1.00  unary:                                  5
% 2.64/1.00  binary:                                 6
% 2.64/1.00  lits:                                   60
% 2.64/1.00  lits_eq:                                6
% 2.64/1.00  fd_pure:                                0
% 2.64/1.00  fd_pseudo:                              0
% 2.64/1.00  fd_cond:                                0
% 2.64/1.00  fd_pseudo_cond:                         4
% 2.64/1.00  ac_symbols:                             0
% 2.64/1.00  
% 2.64/1.00  ------ Propositional Solver
% 2.64/1.00  
% 2.64/1.00  prop_solver_calls:                      25
% 2.64/1.00  prop_fast_solver_calls:                 1010
% 2.64/1.00  smt_solver_calls:                       0
% 2.64/1.00  smt_fast_solver_calls:                  0
% 2.64/1.00  prop_num_of_clauses:                    3817
% 2.64/1.00  prop_preprocess_simplified:             6974
% 2.64/1.00  prop_fo_subsumed:                       110
% 2.64/1.00  prop_solver_time:                       0.
% 2.64/1.00  smt_solver_time:                        0.
% 2.64/1.00  smt_fast_solver_time:                   0.
% 2.64/1.00  prop_fast_solver_time:                  0.
% 2.64/1.00  prop_unsat_core_time:                   0.
% 2.64/1.00  
% 2.64/1.00  ------ QBF
% 2.64/1.00  
% 2.64/1.00  qbf_q_res:                              0
% 2.64/1.00  qbf_num_tautologies:                    0
% 2.64/1.00  qbf_prep_cycles:                        0
% 2.64/1.00  
% 2.64/1.00  ------ BMC1
% 2.64/1.00  
% 2.64/1.00  bmc1_current_bound:                     -1
% 2.64/1.00  bmc1_last_solved_bound:                 -1
% 2.64/1.00  bmc1_unsat_core_size:                   -1
% 2.64/1.00  bmc1_unsat_core_parents_size:           -1
% 2.64/1.00  bmc1_merge_next_fun:                    0
% 2.64/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.64/1.00  
% 2.64/1.00  ------ Instantiation
% 2.64/1.00  
% 2.64/1.00  inst_num_of_clauses:                    951
% 2.64/1.00  inst_num_in_passive:                    35
% 2.64/1.00  inst_num_in_active:                     515
% 2.64/1.00  inst_num_in_unprocessed:                400
% 2.64/1.00  inst_num_of_loops:                      635
% 2.64/1.00  inst_num_of_learning_restarts:          0
% 2.64/1.00  inst_num_moves_active_passive:          115
% 2.64/1.00  inst_lit_activity:                      0
% 2.64/1.00  inst_lit_activity_moves:                0
% 2.64/1.00  inst_num_tautologies:                   0
% 2.64/1.00  inst_num_prop_implied:                  0
% 2.64/1.00  inst_num_existing_simplified:           0
% 2.64/1.00  inst_num_eq_res_simplified:             0
% 2.64/1.00  inst_num_child_elim:                    0
% 2.64/1.00  inst_num_of_dismatching_blockings:      577
% 2.64/1.00  inst_num_of_non_proper_insts:           1095
% 2.64/1.00  inst_num_of_duplicates:                 0
% 2.64/1.00  inst_inst_num_from_inst_to_res:         0
% 2.64/1.00  inst_dismatching_checking_time:         0.
% 2.64/1.00  
% 2.64/1.00  ------ Resolution
% 2.64/1.00  
% 2.64/1.00  res_num_of_clauses:                     0
% 2.64/1.00  res_num_in_passive:                     0
% 2.64/1.00  res_num_in_active:                      0
% 2.64/1.00  res_num_of_loops:                       90
% 2.64/1.00  res_forward_subset_subsumed:            60
% 2.64/1.00  res_backward_subset_subsumed:           0
% 2.64/1.00  res_forward_subsumed:                   0
% 2.64/1.00  res_backward_subsumed:                  0
% 2.64/1.00  res_forward_subsumption_resolution:     0
% 2.64/1.00  res_backward_subsumption_resolution:    0
% 2.64/1.00  res_clause_to_clause_subsumption:       1667
% 2.64/1.00  res_orphan_elimination:                 0
% 2.64/1.00  res_tautology_del:                      25
% 2.64/1.00  res_num_eq_res_simplified:              0
% 2.64/1.00  res_num_sel_changes:                    0
% 2.64/1.00  res_moves_from_active_to_pass:          0
% 2.64/1.00  
% 2.64/1.00  ------ Superposition
% 2.64/1.00  
% 2.64/1.00  sup_time_total:                         0.
% 2.64/1.00  sup_time_generating:                    0.
% 2.64/1.00  sup_time_sim_full:                      0.
% 2.64/1.00  sup_time_sim_immed:                     0.
% 2.64/1.00  
% 2.64/1.00  sup_num_of_clauses:                     290
% 2.64/1.00  sup_num_in_active:                      126
% 2.64/1.00  sup_num_in_passive:                     164
% 2.64/1.00  sup_num_of_loops:                       126
% 2.64/1.00  sup_fw_superposition:                   162
% 2.64/1.00  sup_bw_superposition:                   281
% 2.64/1.00  sup_immediate_simplified:               136
% 2.64/1.00  sup_given_eliminated:                   0
% 2.64/1.00  comparisons_done:                       0
% 2.64/1.00  comparisons_avoided:                    0
% 2.64/1.00  
% 2.64/1.00  ------ Simplifications
% 2.64/1.00  
% 2.64/1.00  
% 2.64/1.00  sim_fw_subset_subsumed:                 83
% 2.64/1.00  sim_bw_subset_subsumed:                 0
% 2.64/1.00  sim_fw_subsumed:                        48
% 2.64/1.00  sim_bw_subsumed:                        0
% 2.64/1.00  sim_fw_subsumption_res:                 0
% 2.64/1.00  sim_bw_subsumption_res:                 0
% 2.64/1.00  sim_tautology_del:                      3
% 2.64/1.00  sim_eq_tautology_del:                   2
% 2.64/1.00  sim_eq_res_simp:                        0
% 2.64/1.00  sim_fw_demodulated:                     7
% 2.64/1.00  sim_bw_demodulated:                     0
% 2.64/1.00  sim_light_normalised:                   0
% 2.64/1.00  sim_joinable_taut:                      0
% 2.64/1.00  sim_joinable_simp:                      0
% 2.64/1.00  sim_ac_normalised:                      0
% 2.64/1.00  sim_smt_subsumption:                    0
% 2.64/1.00  
%------------------------------------------------------------------------------
