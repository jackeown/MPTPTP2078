%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:02 EST 2020

% Result     : Theorem 15.70s
% Output     : CNFRefutation 15.70s
% Verified   : 
% Statistics : Number of formulae       :  171 (2767 expanded)
%              Number of clauses        :   91 ( 844 expanded)
%              Number of leaves         :   21 ( 600 expanded)
%              Depth                    :   23
%              Number of atoms          :  546 (12891 expanded)
%              Number of equality atoms :  398 (8183 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK4,sK5,sK6,sK8) != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK7 = X7
                  | k3_mcart_1(X5,X6,X7) != sK8
                  | ~ m1_subset_1(X7,sK6) )
              | ~ m1_subset_1(X6,sK5) )
          | ~ m1_subset_1(X5,sK4) )
      & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK8) != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK7 = X7
                | k3_mcart_1(X5,X6,X7) != sK8
                | ~ m1_subset_1(X7,sK6) )
            | ~ m1_subset_1(X6,sK5) )
        | ~ m1_subset_1(X5,sK4) )
    & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f43])).

fof(f78,plain,(
    m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f78,f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK1(X0),sK2(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f39])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f84])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f111,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f97])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f101,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f102,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f101])).

fof(f79,plain,(
    ! [X6,X7,X5] :
      ( sK7 = X7
      | k3_mcart_1(X5,X6,X7) != sK8
      | ~ m1_subset_1(X7,sK6)
      | ~ m1_subset_1(X6,sK5)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    ! [X6,X7,X5] :
      ( sK7 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK8
      | ~ m1_subset_1(X7,sK6)
      | ~ m1_subset_1(X6,sK5)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(definition_unfolding,[],[f79,f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f70,f61])).

fof(f83,plain,(
    k7_mcart_1(sK4,sK5,sK6,sK8) != sK7 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_602,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_612,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2233,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_612])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_615,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2375,plain,
    ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_615])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_607,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_622,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1851,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_622])).

cnf(c_2507,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | k4_tarski(sK1(sK8),sK2(sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_2375,c_1851])).

cnf(c_3188,plain,
    ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8
    | m1_subset_1(sK8,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2507,c_602])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_274,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_683,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_684,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_702,plain,
    ( k2_zfmisc_1(X0,sK5) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_825,plain,
    ( k2_zfmisc_1(sK4,sK5) != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_3178,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_xboole_0
    | k4_tarski(sK1(sK8),sK2(sK8)) = sK8
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2507,c_10])).

cnf(c_3439,plain,
    ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3188,c_32,c_31,c_30,c_41,c_42,c_684,c_825,c_3178])).

cnf(c_28,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3441,plain,
    ( k1_mcart_1(sK8) = sK1(sK8) ),
    inference(superposition,[status(thm)],[c_3439,c_28])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_610,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2377,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_610])).

cnf(c_3508,plain,
    ( r2_hidden(sK1(sK8),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_2377])).

cnf(c_4187,plain,
    ( k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_615])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_611,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2072,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK3(k2_zfmisc_1(X0,X1))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_611])).

cnf(c_3637,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_622])).

cnf(c_5426,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = k1_xboole_0
    | k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
    inference(superposition,[status(thm)],[c_4187,c_3637])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_996,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,X0))
    | k2_zfmisc_1(sK4,sK5) = X0
    | k2_zfmisc_1(sK4,sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1792,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK4,sK5)))
    | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK4,sK5)
    | k2_zfmisc_1(sK4,sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1001,plain,
    ( k2_zfmisc_1(sK4,sK5) != X0
    | k2_zfmisc_1(sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1801,plain,
    ( k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
    | k2_zfmisc_1(sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_5428,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
    inference(superposition,[status(thm)],[c_4187,c_1851])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_11115,plain,
    ( r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_667,plain,
    ( k2_zfmisc_1(X0,sK6) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4823,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK6) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_11300,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_4823])).

cnf(c_36222,plain,
    ( k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5426,c_32,c_31,c_30,c_825,c_1792,c_1801,c_5428,c_11115,c_11300])).

cnf(c_33,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ m1_subset_1(X1,sK5)
    | ~ m1_subset_1(X2,sK4)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK8
    | sK7 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_603,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK8
    | sK7 = X2
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36226,plain,
    ( k4_tarski(sK1(sK8),X0) != sK8
    | sK7 = X0
    | m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK2(sK1(sK8)),sK5) != iProver_top
    | m1_subset_1(sK1(sK1(sK8)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_36222,c_603])).

cnf(c_36224,plain,
    ( k1_mcart_1(sK1(sK8)) = sK1(sK1(sK8)) ),
    inference(superposition,[status(thm)],[c_36222,c_28])).

cnf(c_2513,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2377,c_610])).

cnf(c_3932,plain,
    ( r2_hidden(k1_mcart_1(sK1(sK8)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2513,c_3441])).

cnf(c_3936,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK1(sK8)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3932,c_1851])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_613,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4314,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(sK1(sK8)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3936,c_613])).

cnf(c_36329,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(sK1(sK1(sK8)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_36224,c_4314])).

cnf(c_27,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36225,plain,
    ( k2_mcart_1(sK1(sK8)) = sK2(sK1(sK8)) ),
    inference(superposition,[status(thm)],[c_36222,c_27])).

cnf(c_2512,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2377,c_611])).

cnf(c_3859,plain,
    ( r2_hidden(k2_mcart_1(sK1(sK8)),sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2512,c_3441])).

cnf(c_3863,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK1(sK8)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3859,c_1851])).

cnf(c_4258,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK1(sK8)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3863,c_613])).

cnf(c_36372,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(sK2(sK1(sK8)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_36225,c_4258])).

cnf(c_36415,plain,
    ( k4_tarski(sK1(sK8),X0) != sK8
    | sK7 = X0
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36226,c_32,c_31,c_30,c_825,c_1792,c_1801,c_11115,c_11300,c_36329,c_36372])).

cnf(c_36421,plain,
    ( sK2(sK8) = sK7
    | m1_subset_1(sK2(sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3439,c_36415])).

cnf(c_3442,plain,
    ( k2_mcart_1(sK8) = sK2(sK8) ),
    inference(superposition,[status(thm)],[c_3439,c_27])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_606,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2192,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK8) = k2_mcart_1(sK8)
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_602,c_606])).

cnf(c_718,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_719,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_745,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_746,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_2381,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK8) = k2_mcart_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2192,c_32,c_31,c_30,c_41,c_42,c_684,c_719,c_746])).

cnf(c_29,negated_conjecture,
    ( k7_mcart_1(sK4,sK5,sK6,sK8) != sK7 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2383,plain,
    ( k2_mcart_1(sK8) != sK7 ),
    inference(demodulation,[status(thm)],[c_2381,c_29])).

cnf(c_3515,plain,
    ( sK2(sK8) != sK7 ),
    inference(demodulation,[status(thm)],[c_3442,c_2383])).

cnf(c_2376,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK6) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_611])).

cnf(c_2432,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_1851])).

cnf(c_2578,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_613])).

cnf(c_3512,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | m1_subset_1(sK2(sK8),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3442,c_2578])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36421,c_11300,c_11115,c_3515,c_3512,c_1801,c_1792,c_825,c_30,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.70/2.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.70/2.55  
% 15.70/2.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.70/2.55  
% 15.70/2.55  ------  iProver source info
% 15.70/2.55  
% 15.70/2.55  git: date: 2020-06-30 10:37:57 +0100
% 15.70/2.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.70/2.55  git: non_committed_changes: false
% 15.70/2.55  git: last_make_outside_of_git: false
% 15.70/2.55  
% 15.70/2.55  ------ 
% 15.70/2.55  
% 15.70/2.55  ------ Input Options
% 15.70/2.55  
% 15.70/2.55  --out_options                           all
% 15.70/2.55  --tptp_safe_out                         true
% 15.70/2.55  --problem_path                          ""
% 15.70/2.55  --include_path                          ""
% 15.70/2.55  --clausifier                            res/vclausify_rel
% 15.70/2.55  --clausifier_options                    ""
% 15.70/2.55  --stdin                                 false
% 15.70/2.55  --stats_out                             all
% 15.70/2.55  
% 15.70/2.55  ------ General Options
% 15.70/2.55  
% 15.70/2.55  --fof                                   false
% 15.70/2.55  --time_out_real                         305.
% 15.70/2.55  --time_out_virtual                      -1.
% 15.70/2.55  --symbol_type_check                     false
% 15.70/2.55  --clausify_out                          false
% 15.70/2.55  --sig_cnt_out                           false
% 15.70/2.55  --trig_cnt_out                          false
% 15.70/2.55  --trig_cnt_out_tolerance                1.
% 15.70/2.55  --trig_cnt_out_sk_spl                   false
% 15.70/2.55  --abstr_cl_out                          false
% 15.70/2.55  
% 15.70/2.55  ------ Global Options
% 15.70/2.55  
% 15.70/2.55  --schedule                              default
% 15.70/2.55  --add_important_lit                     false
% 15.70/2.55  --prop_solver_per_cl                    1000
% 15.70/2.55  --min_unsat_core                        false
% 15.70/2.55  --soft_assumptions                      false
% 15.70/2.55  --soft_lemma_size                       3
% 15.70/2.55  --prop_impl_unit_size                   0
% 15.70/2.55  --prop_impl_unit                        []
% 15.70/2.55  --share_sel_clauses                     true
% 15.70/2.55  --reset_solvers                         false
% 15.70/2.55  --bc_imp_inh                            [conj_cone]
% 15.70/2.55  --conj_cone_tolerance                   3.
% 15.70/2.55  --extra_neg_conj                        none
% 15.70/2.55  --large_theory_mode                     true
% 15.70/2.55  --prolific_symb_bound                   200
% 15.70/2.55  --lt_threshold                          2000
% 15.70/2.55  --clause_weak_htbl                      true
% 15.70/2.55  --gc_record_bc_elim                     false
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing Options
% 15.70/2.55  
% 15.70/2.55  --preprocessing_flag                    true
% 15.70/2.55  --time_out_prep_mult                    0.1
% 15.70/2.55  --splitting_mode                        input
% 15.70/2.55  --splitting_grd                         true
% 15.70/2.55  --splitting_cvd                         false
% 15.70/2.55  --splitting_cvd_svl                     false
% 15.70/2.55  --splitting_nvd                         32
% 15.70/2.55  --sub_typing                            true
% 15.70/2.55  --prep_gs_sim                           true
% 15.70/2.55  --prep_unflatten                        true
% 15.70/2.55  --prep_res_sim                          true
% 15.70/2.55  --prep_upred                            true
% 15.70/2.55  --prep_sem_filter                       exhaustive
% 15.70/2.55  --prep_sem_filter_out                   false
% 15.70/2.55  --pred_elim                             true
% 15.70/2.55  --res_sim_input                         true
% 15.70/2.55  --eq_ax_congr_red                       true
% 15.70/2.55  --pure_diseq_elim                       true
% 15.70/2.55  --brand_transform                       false
% 15.70/2.55  --non_eq_to_eq                          false
% 15.70/2.55  --prep_def_merge                        true
% 15.70/2.55  --prep_def_merge_prop_impl              false
% 15.70/2.55  --prep_def_merge_mbd                    true
% 15.70/2.55  --prep_def_merge_tr_red                 false
% 15.70/2.55  --prep_def_merge_tr_cl                  false
% 15.70/2.55  --smt_preprocessing                     true
% 15.70/2.55  --smt_ac_axioms                         fast
% 15.70/2.55  --preprocessed_out                      false
% 15.70/2.55  --preprocessed_stats                    false
% 15.70/2.55  
% 15.70/2.55  ------ Abstraction refinement Options
% 15.70/2.55  
% 15.70/2.55  --abstr_ref                             []
% 15.70/2.55  --abstr_ref_prep                        false
% 15.70/2.55  --abstr_ref_until_sat                   false
% 15.70/2.55  --abstr_ref_sig_restrict                funpre
% 15.70/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.70/2.55  --abstr_ref_under                       []
% 15.70/2.55  
% 15.70/2.55  ------ SAT Options
% 15.70/2.55  
% 15.70/2.55  --sat_mode                              false
% 15.70/2.55  --sat_fm_restart_options                ""
% 15.70/2.55  --sat_gr_def                            false
% 15.70/2.55  --sat_epr_types                         true
% 15.70/2.55  --sat_non_cyclic_types                  false
% 15.70/2.55  --sat_finite_models                     false
% 15.70/2.55  --sat_fm_lemmas                         false
% 15.70/2.55  --sat_fm_prep                           false
% 15.70/2.55  --sat_fm_uc_incr                        true
% 15.70/2.55  --sat_out_model                         small
% 15.70/2.55  --sat_out_clauses                       false
% 15.70/2.55  
% 15.70/2.55  ------ QBF Options
% 15.70/2.55  
% 15.70/2.55  --qbf_mode                              false
% 15.70/2.55  --qbf_elim_univ                         false
% 15.70/2.55  --qbf_dom_inst                          none
% 15.70/2.55  --qbf_dom_pre_inst                      false
% 15.70/2.55  --qbf_sk_in                             false
% 15.70/2.55  --qbf_pred_elim                         true
% 15.70/2.55  --qbf_split                             512
% 15.70/2.55  
% 15.70/2.55  ------ BMC1 Options
% 15.70/2.55  
% 15.70/2.55  --bmc1_incremental                      false
% 15.70/2.55  --bmc1_axioms                           reachable_all
% 15.70/2.55  --bmc1_min_bound                        0
% 15.70/2.55  --bmc1_max_bound                        -1
% 15.70/2.55  --bmc1_max_bound_default                -1
% 15.70/2.55  --bmc1_symbol_reachability              true
% 15.70/2.55  --bmc1_property_lemmas                  false
% 15.70/2.55  --bmc1_k_induction                      false
% 15.70/2.55  --bmc1_non_equiv_states                 false
% 15.70/2.55  --bmc1_deadlock                         false
% 15.70/2.55  --bmc1_ucm                              false
% 15.70/2.55  --bmc1_add_unsat_core                   none
% 15.70/2.55  --bmc1_unsat_core_children              false
% 15.70/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.70/2.55  --bmc1_out_stat                         full
% 15.70/2.55  --bmc1_ground_init                      false
% 15.70/2.55  --bmc1_pre_inst_next_state              false
% 15.70/2.55  --bmc1_pre_inst_state                   false
% 15.70/2.55  --bmc1_pre_inst_reach_state             false
% 15.70/2.55  --bmc1_out_unsat_core                   false
% 15.70/2.55  --bmc1_aig_witness_out                  false
% 15.70/2.55  --bmc1_verbose                          false
% 15.70/2.55  --bmc1_dump_clauses_tptp                false
% 15.70/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.70/2.55  --bmc1_dump_file                        -
% 15.70/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.70/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.70/2.55  --bmc1_ucm_extend_mode                  1
% 15.70/2.55  --bmc1_ucm_init_mode                    2
% 15.70/2.55  --bmc1_ucm_cone_mode                    none
% 15.70/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.70/2.55  --bmc1_ucm_relax_model                  4
% 15.70/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.70/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.70/2.55  --bmc1_ucm_layered_model                none
% 15.70/2.55  --bmc1_ucm_max_lemma_size               10
% 15.70/2.55  
% 15.70/2.55  ------ AIG Options
% 15.70/2.55  
% 15.70/2.55  --aig_mode                              false
% 15.70/2.55  
% 15.70/2.55  ------ Instantiation Options
% 15.70/2.55  
% 15.70/2.55  --instantiation_flag                    true
% 15.70/2.55  --inst_sos_flag                         true
% 15.70/2.55  --inst_sos_phase                        true
% 15.70/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.70/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.70/2.55  --inst_lit_sel_side                     num_symb
% 15.70/2.55  --inst_solver_per_active                1400
% 15.70/2.55  --inst_solver_calls_frac                1.
% 15.70/2.55  --inst_passive_queue_type               priority_queues
% 15.70/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.70/2.55  --inst_passive_queues_freq              [25;2]
% 15.70/2.55  --inst_dismatching                      true
% 15.70/2.55  --inst_eager_unprocessed_to_passive     true
% 15.70/2.55  --inst_prop_sim_given                   true
% 15.70/2.55  --inst_prop_sim_new                     false
% 15.70/2.55  --inst_subs_new                         false
% 15.70/2.55  --inst_eq_res_simp                      false
% 15.70/2.55  --inst_subs_given                       false
% 15.70/2.55  --inst_orphan_elimination               true
% 15.70/2.55  --inst_learning_loop_flag               true
% 15.70/2.55  --inst_learning_start                   3000
% 15.70/2.55  --inst_learning_factor                  2
% 15.70/2.55  --inst_start_prop_sim_after_learn       3
% 15.70/2.55  --inst_sel_renew                        solver
% 15.70/2.55  --inst_lit_activity_flag                true
% 15.70/2.55  --inst_restr_to_given                   false
% 15.70/2.55  --inst_activity_threshold               500
% 15.70/2.55  --inst_out_proof                        true
% 15.70/2.55  
% 15.70/2.55  ------ Resolution Options
% 15.70/2.55  
% 15.70/2.55  --resolution_flag                       true
% 15.70/2.55  --res_lit_sel                           adaptive
% 15.70/2.55  --res_lit_sel_side                      none
% 15.70/2.55  --res_ordering                          kbo
% 15.70/2.55  --res_to_prop_solver                    active
% 15.70/2.55  --res_prop_simpl_new                    false
% 15.70/2.55  --res_prop_simpl_given                  true
% 15.70/2.55  --res_passive_queue_type                priority_queues
% 15.70/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.70/2.55  --res_passive_queues_freq               [15;5]
% 15.70/2.55  --res_forward_subs                      full
% 15.70/2.55  --res_backward_subs                     full
% 15.70/2.55  --res_forward_subs_resolution           true
% 15.70/2.55  --res_backward_subs_resolution          true
% 15.70/2.55  --res_orphan_elimination                true
% 15.70/2.55  --res_time_limit                        2.
% 15.70/2.55  --res_out_proof                         true
% 15.70/2.55  
% 15.70/2.55  ------ Superposition Options
% 15.70/2.55  
% 15.70/2.55  --superposition_flag                    true
% 15.70/2.55  --sup_passive_queue_type                priority_queues
% 15.70/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.70/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.70/2.55  --demod_completeness_check              fast
% 15.70/2.55  --demod_use_ground                      true
% 15.70/2.55  --sup_to_prop_solver                    passive
% 15.70/2.55  --sup_prop_simpl_new                    true
% 15.70/2.55  --sup_prop_simpl_given                  true
% 15.70/2.55  --sup_fun_splitting                     true
% 15.70/2.55  --sup_smt_interval                      50000
% 15.70/2.55  
% 15.70/2.55  ------ Superposition Simplification Setup
% 15.70/2.55  
% 15.70/2.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.70/2.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.70/2.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.70/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.70/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.70/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.70/2.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.70/2.55  --sup_immed_triv                        [TrivRules]
% 15.70/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_immed_bw_main                     []
% 15.70/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.70/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.70/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_input_bw                          []
% 15.70/2.55  
% 15.70/2.55  ------ Combination Options
% 15.70/2.55  
% 15.70/2.55  --comb_res_mult                         3
% 15.70/2.55  --comb_sup_mult                         2
% 15.70/2.55  --comb_inst_mult                        10
% 15.70/2.55  
% 15.70/2.55  ------ Debug Options
% 15.70/2.55  
% 15.70/2.55  --dbg_backtrace                         false
% 15.70/2.55  --dbg_dump_prop_clauses                 false
% 15.70/2.55  --dbg_dump_prop_clauses_file            -
% 15.70/2.55  --dbg_out_stat                          false
% 15.70/2.55  ------ Parsing...
% 15.70/2.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.70/2.55  ------ Proving...
% 15.70/2.55  ------ Problem Properties 
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  clauses                                 35
% 15.70/2.55  conjectures                             6
% 15.70/2.55  EPR                                     6
% 15.70/2.55  Horn                                    26
% 15.70/2.55  unary                                   16
% 15.70/2.55  binary                                  6
% 15.70/2.55  lits                                    78
% 15.70/2.55  lits eq                                 49
% 15.70/2.55  fd_pure                                 0
% 15.70/2.55  fd_pseudo                               0
% 15.70/2.55  fd_cond                                 9
% 15.70/2.55  fd_pseudo_cond                          3
% 15.70/2.55  AC symbols                              0
% 15.70/2.55  
% 15.70/2.55  ------ Schedule dynamic 5 is on 
% 15.70/2.55  
% 15.70/2.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  ------ 
% 15.70/2.55  Current options:
% 15.70/2.55  ------ 
% 15.70/2.55  
% 15.70/2.55  ------ Input Options
% 15.70/2.55  
% 15.70/2.55  --out_options                           all
% 15.70/2.55  --tptp_safe_out                         true
% 15.70/2.55  --problem_path                          ""
% 15.70/2.55  --include_path                          ""
% 15.70/2.55  --clausifier                            res/vclausify_rel
% 15.70/2.55  --clausifier_options                    ""
% 15.70/2.55  --stdin                                 false
% 15.70/2.55  --stats_out                             all
% 15.70/2.55  
% 15.70/2.55  ------ General Options
% 15.70/2.55  
% 15.70/2.55  --fof                                   false
% 15.70/2.55  --time_out_real                         305.
% 15.70/2.55  --time_out_virtual                      -1.
% 15.70/2.55  --symbol_type_check                     false
% 15.70/2.55  --clausify_out                          false
% 15.70/2.55  --sig_cnt_out                           false
% 15.70/2.55  --trig_cnt_out                          false
% 15.70/2.55  --trig_cnt_out_tolerance                1.
% 15.70/2.55  --trig_cnt_out_sk_spl                   false
% 15.70/2.55  --abstr_cl_out                          false
% 15.70/2.55  
% 15.70/2.55  ------ Global Options
% 15.70/2.55  
% 15.70/2.55  --schedule                              default
% 15.70/2.55  --add_important_lit                     false
% 15.70/2.55  --prop_solver_per_cl                    1000
% 15.70/2.55  --min_unsat_core                        false
% 15.70/2.55  --soft_assumptions                      false
% 15.70/2.55  --soft_lemma_size                       3
% 15.70/2.55  --prop_impl_unit_size                   0
% 15.70/2.55  --prop_impl_unit                        []
% 15.70/2.55  --share_sel_clauses                     true
% 15.70/2.55  --reset_solvers                         false
% 15.70/2.55  --bc_imp_inh                            [conj_cone]
% 15.70/2.55  --conj_cone_tolerance                   3.
% 15.70/2.55  --extra_neg_conj                        none
% 15.70/2.55  --large_theory_mode                     true
% 15.70/2.55  --prolific_symb_bound                   200
% 15.70/2.55  --lt_threshold                          2000
% 15.70/2.55  --clause_weak_htbl                      true
% 15.70/2.55  --gc_record_bc_elim                     false
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing Options
% 15.70/2.55  
% 15.70/2.55  --preprocessing_flag                    true
% 15.70/2.55  --time_out_prep_mult                    0.1
% 15.70/2.55  --splitting_mode                        input
% 15.70/2.55  --splitting_grd                         true
% 15.70/2.55  --splitting_cvd                         false
% 15.70/2.55  --splitting_cvd_svl                     false
% 15.70/2.55  --splitting_nvd                         32
% 15.70/2.55  --sub_typing                            true
% 15.70/2.55  --prep_gs_sim                           true
% 15.70/2.55  --prep_unflatten                        true
% 15.70/2.55  --prep_res_sim                          true
% 15.70/2.55  --prep_upred                            true
% 15.70/2.55  --prep_sem_filter                       exhaustive
% 15.70/2.55  --prep_sem_filter_out                   false
% 15.70/2.55  --pred_elim                             true
% 15.70/2.55  --res_sim_input                         true
% 15.70/2.55  --eq_ax_congr_red                       true
% 15.70/2.55  --pure_diseq_elim                       true
% 15.70/2.55  --brand_transform                       false
% 15.70/2.55  --non_eq_to_eq                          false
% 15.70/2.55  --prep_def_merge                        true
% 15.70/2.55  --prep_def_merge_prop_impl              false
% 15.70/2.55  --prep_def_merge_mbd                    true
% 15.70/2.55  --prep_def_merge_tr_red                 false
% 15.70/2.55  --prep_def_merge_tr_cl                  false
% 15.70/2.55  --smt_preprocessing                     true
% 15.70/2.55  --smt_ac_axioms                         fast
% 15.70/2.55  --preprocessed_out                      false
% 15.70/2.55  --preprocessed_stats                    false
% 15.70/2.55  
% 15.70/2.55  ------ Abstraction refinement Options
% 15.70/2.55  
% 15.70/2.55  --abstr_ref                             []
% 15.70/2.55  --abstr_ref_prep                        false
% 15.70/2.55  --abstr_ref_until_sat                   false
% 15.70/2.55  --abstr_ref_sig_restrict                funpre
% 15.70/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.70/2.55  --abstr_ref_under                       []
% 15.70/2.55  
% 15.70/2.55  ------ SAT Options
% 15.70/2.55  
% 15.70/2.55  --sat_mode                              false
% 15.70/2.55  --sat_fm_restart_options                ""
% 15.70/2.55  --sat_gr_def                            false
% 15.70/2.55  --sat_epr_types                         true
% 15.70/2.55  --sat_non_cyclic_types                  false
% 15.70/2.55  --sat_finite_models                     false
% 15.70/2.55  --sat_fm_lemmas                         false
% 15.70/2.55  --sat_fm_prep                           false
% 15.70/2.55  --sat_fm_uc_incr                        true
% 15.70/2.55  --sat_out_model                         small
% 15.70/2.55  --sat_out_clauses                       false
% 15.70/2.55  
% 15.70/2.55  ------ QBF Options
% 15.70/2.55  
% 15.70/2.55  --qbf_mode                              false
% 15.70/2.55  --qbf_elim_univ                         false
% 15.70/2.55  --qbf_dom_inst                          none
% 15.70/2.55  --qbf_dom_pre_inst                      false
% 15.70/2.55  --qbf_sk_in                             false
% 15.70/2.55  --qbf_pred_elim                         true
% 15.70/2.55  --qbf_split                             512
% 15.70/2.55  
% 15.70/2.55  ------ BMC1 Options
% 15.70/2.55  
% 15.70/2.55  --bmc1_incremental                      false
% 15.70/2.55  --bmc1_axioms                           reachable_all
% 15.70/2.55  --bmc1_min_bound                        0
% 15.70/2.55  --bmc1_max_bound                        -1
% 15.70/2.55  --bmc1_max_bound_default                -1
% 15.70/2.55  --bmc1_symbol_reachability              true
% 15.70/2.55  --bmc1_property_lemmas                  false
% 15.70/2.55  --bmc1_k_induction                      false
% 15.70/2.55  --bmc1_non_equiv_states                 false
% 15.70/2.55  --bmc1_deadlock                         false
% 15.70/2.55  --bmc1_ucm                              false
% 15.70/2.55  --bmc1_add_unsat_core                   none
% 15.70/2.55  --bmc1_unsat_core_children              false
% 15.70/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.70/2.55  --bmc1_out_stat                         full
% 15.70/2.55  --bmc1_ground_init                      false
% 15.70/2.55  --bmc1_pre_inst_next_state              false
% 15.70/2.55  --bmc1_pre_inst_state                   false
% 15.70/2.55  --bmc1_pre_inst_reach_state             false
% 15.70/2.55  --bmc1_out_unsat_core                   false
% 15.70/2.55  --bmc1_aig_witness_out                  false
% 15.70/2.55  --bmc1_verbose                          false
% 15.70/2.55  --bmc1_dump_clauses_tptp                false
% 15.70/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.70/2.55  --bmc1_dump_file                        -
% 15.70/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.70/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.70/2.55  --bmc1_ucm_extend_mode                  1
% 15.70/2.55  --bmc1_ucm_init_mode                    2
% 15.70/2.55  --bmc1_ucm_cone_mode                    none
% 15.70/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.70/2.55  --bmc1_ucm_relax_model                  4
% 15.70/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.70/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.70/2.55  --bmc1_ucm_layered_model                none
% 15.70/2.55  --bmc1_ucm_max_lemma_size               10
% 15.70/2.55  
% 15.70/2.55  ------ AIG Options
% 15.70/2.55  
% 15.70/2.55  --aig_mode                              false
% 15.70/2.55  
% 15.70/2.55  ------ Instantiation Options
% 15.70/2.55  
% 15.70/2.55  --instantiation_flag                    true
% 15.70/2.55  --inst_sos_flag                         true
% 15.70/2.55  --inst_sos_phase                        true
% 15.70/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.70/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.70/2.55  --inst_lit_sel_side                     none
% 15.70/2.55  --inst_solver_per_active                1400
% 15.70/2.55  --inst_solver_calls_frac                1.
% 15.70/2.55  --inst_passive_queue_type               priority_queues
% 15.70/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.70/2.55  --inst_passive_queues_freq              [25;2]
% 15.70/2.55  --inst_dismatching                      true
% 15.70/2.55  --inst_eager_unprocessed_to_passive     true
% 15.70/2.55  --inst_prop_sim_given                   true
% 15.70/2.55  --inst_prop_sim_new                     false
% 15.70/2.55  --inst_subs_new                         false
% 15.70/2.55  --inst_eq_res_simp                      false
% 15.70/2.55  --inst_subs_given                       false
% 15.70/2.55  --inst_orphan_elimination               true
% 15.70/2.55  --inst_learning_loop_flag               true
% 15.70/2.55  --inst_learning_start                   3000
% 15.70/2.55  --inst_learning_factor                  2
% 15.70/2.55  --inst_start_prop_sim_after_learn       3
% 15.70/2.55  --inst_sel_renew                        solver
% 15.70/2.55  --inst_lit_activity_flag                true
% 15.70/2.55  --inst_restr_to_given                   false
% 15.70/2.55  --inst_activity_threshold               500
% 15.70/2.55  --inst_out_proof                        true
% 15.70/2.55  
% 15.70/2.55  ------ Resolution Options
% 15.70/2.55  
% 15.70/2.55  --resolution_flag                       false
% 15.70/2.55  --res_lit_sel                           adaptive
% 15.70/2.55  --res_lit_sel_side                      none
% 15.70/2.55  --res_ordering                          kbo
% 15.70/2.55  --res_to_prop_solver                    active
% 15.70/2.55  --res_prop_simpl_new                    false
% 15.70/2.55  --res_prop_simpl_given                  true
% 15.70/2.55  --res_passive_queue_type                priority_queues
% 15.70/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.70/2.55  --res_passive_queues_freq               [15;5]
% 15.70/2.55  --res_forward_subs                      full
% 15.70/2.55  --res_backward_subs                     full
% 15.70/2.55  --res_forward_subs_resolution           true
% 15.70/2.55  --res_backward_subs_resolution          true
% 15.70/2.55  --res_orphan_elimination                true
% 15.70/2.55  --res_time_limit                        2.
% 15.70/2.55  --res_out_proof                         true
% 15.70/2.55  
% 15.70/2.55  ------ Superposition Options
% 15.70/2.55  
% 15.70/2.55  --superposition_flag                    true
% 15.70/2.55  --sup_passive_queue_type                priority_queues
% 15.70/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.70/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.70/2.55  --demod_completeness_check              fast
% 15.70/2.55  --demod_use_ground                      true
% 15.70/2.55  --sup_to_prop_solver                    passive
% 15.70/2.55  --sup_prop_simpl_new                    true
% 15.70/2.55  --sup_prop_simpl_given                  true
% 15.70/2.55  --sup_fun_splitting                     true
% 15.70/2.55  --sup_smt_interval                      50000
% 15.70/2.55  
% 15.70/2.55  ------ Superposition Simplification Setup
% 15.70/2.55  
% 15.70/2.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.70/2.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.70/2.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.70/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.70/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.70/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.70/2.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.70/2.55  --sup_immed_triv                        [TrivRules]
% 15.70/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_immed_bw_main                     []
% 15.70/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.70/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.70/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.55  --sup_input_bw                          []
% 15.70/2.55  
% 15.70/2.55  ------ Combination Options
% 15.70/2.55  
% 15.70/2.55  --comb_res_mult                         3
% 15.70/2.55  --comb_sup_mult                         2
% 15.70/2.55  --comb_inst_mult                        10
% 15.70/2.55  
% 15.70/2.55  ------ Debug Options
% 15.70/2.55  
% 15.70/2.55  --dbg_backtrace                         false
% 15.70/2.55  --dbg_dump_prop_clauses                 false
% 15.70/2.55  --dbg_dump_prop_clauses_file            -
% 15.70/2.55  --dbg_out_stat                          false
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  ------ Proving...
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  % SZS status Theorem for theBenchmark.p
% 15.70/2.55  
% 15.70/2.55  % SZS output start CNFRefutation for theBenchmark.p
% 15.70/2.55  
% 15.70/2.55  fof(f17,conjecture,(
% 15.70/2.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f18,negated_conjecture,(
% 15.70/2.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.70/2.55    inference(negated_conjecture,[],[f17])).
% 15.70/2.55  
% 15.70/2.55  fof(f28,plain,(
% 15.70/2.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 15.70/2.55    inference(ennf_transformation,[],[f18])).
% 15.70/2.55  
% 15.70/2.55  fof(f29,plain,(
% 15.70/2.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 15.70/2.55    inference(flattening,[],[f28])).
% 15.70/2.55  
% 15.70/2.55  fof(f43,plain,(
% 15.70/2.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK4,sK5,sK6,sK8) != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X5] : (! [X6] : (! [X7] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6)) | ~m1_subset_1(X6,sK5)) | ~m1_subset_1(X5,sK4)) & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6)))),
% 15.70/2.55    introduced(choice_axiom,[])).
% 15.70/2.55  
% 15.70/2.55  fof(f44,plain,(
% 15.70/2.55    k7_mcart_1(sK4,sK5,sK6,sK8) != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & ! [X5] : (! [X6] : (! [X7] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6)) | ~m1_subset_1(X6,sK5)) | ~m1_subset_1(X5,sK4)) & m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6))),
% 15.70/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f43])).
% 15.70/2.55  
% 15.70/2.55  fof(f78,plain,(
% 15.70/2.55    m1_subset_1(sK8,k3_zfmisc_1(sK4,sK5,sK6))),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  fof(f10,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f61,plain,(
% 15.70/2.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f10])).
% 15.70/2.55  
% 15.70/2.55  fof(f100,plain,(
% 15.70/2.55    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 15.70/2.55    inference(definition_unfolding,[],[f78,f61])).
% 15.70/2.55  
% 15.70/2.55  fof(f8,axiom,(
% 15.70/2.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f23,plain,(
% 15.70/2.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.70/2.55    inference(ennf_transformation,[],[f8])).
% 15.70/2.55  
% 15.70/2.55  fof(f24,plain,(
% 15.70/2.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.70/2.55    inference(flattening,[],[f23])).
% 15.70/2.55  
% 15.70/2.55  fof(f59,plain,(
% 15.70/2.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f24])).
% 15.70/2.55  
% 15.70/2.55  fof(f4,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f21,plain,(
% 15.70/2.55    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.70/2.55    inference(ennf_transformation,[],[f4])).
% 15.70/2.55  
% 15.70/2.55  fof(f35,plain,(
% 15.70/2.55    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK1(X0),sK2(X0)) = X0)),
% 15.70/2.55    introduced(choice_axiom,[])).
% 15.70/2.55  
% 15.70/2.55  fof(f36,plain,(
% 15.70/2.55    ! [X0,X1,X2] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.70/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f35])).
% 15.70/2.55  
% 15.70/2.55  fof(f53,plain,(
% 15.70/2.55    ( ! [X2,X0,X1] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 15.70/2.55    inference(cnf_transformation,[],[f36])).
% 15.70/2.55  
% 15.70/2.55  fof(f13,axiom,(
% 15.70/2.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f26,plain,(
% 15.70/2.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 15.70/2.55    inference(ennf_transformation,[],[f13])).
% 15.70/2.55  
% 15.70/2.55  fof(f39,plain,(
% 15.70/2.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 15.70/2.55    introduced(choice_axiom,[])).
% 15.70/2.55  
% 15.70/2.55  fof(f40,plain,(
% 15.70/2.55    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 15.70/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f39])).
% 15.70/2.55  
% 15.70/2.55  fof(f65,plain,(
% 15.70/2.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 15.70/2.55    inference(cnf_transformation,[],[f40])).
% 15.70/2.55  
% 15.70/2.55  fof(f1,axiom,(
% 15.70/2.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f19,plain,(
% 15.70/2.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 15.70/2.55    inference(unused_predicate_definition_removal,[],[f1])).
% 15.70/2.55  
% 15.70/2.55  fof(f20,plain,(
% 15.70/2.55    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 15.70/2.55    inference(ennf_transformation,[],[f19])).
% 15.70/2.55  
% 15.70/2.55  fof(f45,plain,(
% 15.70/2.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f20])).
% 15.70/2.55  
% 15.70/2.55  fof(f80,plain,(
% 15.70/2.55    k1_xboole_0 != sK4),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  fof(f81,plain,(
% 15.70/2.55    k1_xboole_0 != sK5),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  fof(f82,plain,(
% 15.70/2.55    k1_xboole_0 != sK6),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  fof(f15,axiom,(
% 15.70/2.55    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f41,plain,(
% 15.70/2.55    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.70/2.55    inference(nnf_transformation,[],[f15])).
% 15.70/2.55  
% 15.70/2.55  fof(f42,plain,(
% 15.70/2.55    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.70/2.55    inference(flattening,[],[f41])).
% 15.70/2.55  
% 15.70/2.55  fof(f71,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.70/2.55    inference(cnf_transformation,[],[f42])).
% 15.70/2.55  
% 15.70/2.55  fof(f11,axiom,(
% 15.70/2.55    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f62,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f11])).
% 15.70/2.55  
% 15.70/2.55  fof(f84,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.70/2.55    inference(definition_unfolding,[],[f62,f61])).
% 15.70/2.55  
% 15.70/2.55  fof(f98,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.70/2.55    inference(definition_unfolding,[],[f71,f84])).
% 15.70/2.55  
% 15.70/2.55  fof(f72,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f42])).
% 15.70/2.55  
% 15.70/2.55  fof(f97,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 15.70/2.55    inference(definition_unfolding,[],[f72,f84])).
% 15.70/2.55  
% 15.70/2.55  fof(f111,plain,(
% 15.70/2.55    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 15.70/2.55    inference(equality_resolution,[],[f97])).
% 15.70/2.55  
% 15.70/2.55  fof(f5,axiom,(
% 15.70/2.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f37,plain,(
% 15.70/2.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.70/2.55    inference(nnf_transformation,[],[f5])).
% 15.70/2.55  
% 15.70/2.55  fof(f38,plain,(
% 15.70/2.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.70/2.55    inference(flattening,[],[f37])).
% 15.70/2.55  
% 15.70/2.55  fof(f54,plain,(
% 15.70/2.55    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 15.70/2.55    inference(cnf_transformation,[],[f38])).
% 15.70/2.55  
% 15.70/2.55  fof(f16,axiom,(
% 15.70/2.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f76,plain,(
% 15.70/2.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 15.70/2.55    inference(cnf_transformation,[],[f16])).
% 15.70/2.55  
% 15.70/2.55  fof(f12,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f25,plain,(
% 15.70/2.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.70/2.55    inference(ennf_transformation,[],[f12])).
% 15.70/2.55  
% 15.70/2.55  fof(f63,plain,(
% 15.70/2.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 15.70/2.55    inference(cnf_transformation,[],[f25])).
% 15.70/2.55  
% 15.70/2.55  fof(f64,plain,(
% 15.70/2.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 15.70/2.55    inference(cnf_transformation,[],[f25])).
% 15.70/2.55  
% 15.70/2.55  fof(f2,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f30,plain,(
% 15.70/2.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 15.70/2.55    inference(nnf_transformation,[],[f2])).
% 15.70/2.55  
% 15.70/2.55  fof(f31,plain,(
% 15.70/2.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 15.70/2.55    inference(flattening,[],[f30])).
% 15.70/2.55  
% 15.70/2.55  fof(f32,plain,(
% 15.70/2.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 15.70/2.55    inference(rectify,[],[f31])).
% 15.70/2.55  
% 15.70/2.55  fof(f33,plain,(
% 15.70/2.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.70/2.55    introduced(choice_axiom,[])).
% 15.70/2.55  
% 15.70/2.55  fof(f34,plain,(
% 15.70/2.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 15.70/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 15.70/2.55  
% 15.70/2.55  fof(f46,plain,(
% 15.70/2.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 15.70/2.55    inference(cnf_transformation,[],[f34])).
% 15.70/2.55  
% 15.70/2.55  fof(f3,axiom,(
% 15.70/2.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f52,plain,(
% 15.70/2.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f3])).
% 15.70/2.55  
% 15.70/2.55  fof(f90,plain,(
% 15.70/2.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 15.70/2.55    inference(definition_unfolding,[],[f46,f52])).
% 15.70/2.55  
% 15.70/2.55  fof(f105,plain,(
% 15.70/2.55    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 15.70/2.55    inference(equality_resolution,[],[f90])).
% 15.70/2.55  
% 15.70/2.55  fof(f48,plain,(
% 15.70/2.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 15.70/2.55    inference(cnf_transformation,[],[f34])).
% 15.70/2.55  
% 15.70/2.55  fof(f88,plain,(
% 15.70/2.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 15.70/2.55    inference(definition_unfolding,[],[f48,f52])).
% 15.70/2.55  
% 15.70/2.55  fof(f101,plain,(
% 15.70/2.55    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 15.70/2.55    inference(equality_resolution,[],[f88])).
% 15.70/2.55  
% 15.70/2.55  fof(f102,plain,(
% 15.70/2.55    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 15.70/2.55    inference(equality_resolution,[],[f101])).
% 15.70/2.55  
% 15.70/2.55  fof(f79,plain,(
% 15.70/2.55    ( ! [X6,X7,X5] : (sK7 = X7 | k3_mcart_1(X5,X6,X7) != sK8 | ~m1_subset_1(X7,sK6) | ~m1_subset_1(X6,sK5) | ~m1_subset_1(X5,sK4)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  fof(f9,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f60,plain,(
% 15.70/2.55    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f9])).
% 15.70/2.55  
% 15.70/2.55  fof(f99,plain,(
% 15.70/2.55    ( ! [X6,X7,X5] : (sK7 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK8 | ~m1_subset_1(X7,sK6) | ~m1_subset_1(X6,sK5) | ~m1_subset_1(X5,sK4)) )),
% 15.70/2.55    inference(definition_unfolding,[],[f79,f60])).
% 15.70/2.55  
% 15.70/2.55  fof(f7,axiom,(
% 15.70/2.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f22,plain,(
% 15.70/2.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 15.70/2.55    inference(ennf_transformation,[],[f7])).
% 15.70/2.55  
% 15.70/2.55  fof(f58,plain,(
% 15.70/2.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 15.70/2.55    inference(cnf_transformation,[],[f22])).
% 15.70/2.55  
% 15.70/2.55  fof(f77,plain,(
% 15.70/2.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 15.70/2.55    inference(cnf_transformation,[],[f16])).
% 15.70/2.55  
% 15.70/2.55  fof(f14,axiom,(
% 15.70/2.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 15.70/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.55  
% 15.70/2.55  fof(f27,plain,(
% 15.70/2.55    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 15.70/2.55    inference(ennf_transformation,[],[f14])).
% 15.70/2.55  
% 15.70/2.55  fof(f70,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.70/2.55    inference(cnf_transformation,[],[f27])).
% 15.70/2.55  
% 15.70/2.55  fof(f91,plain,(
% 15.70/2.55    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.70/2.55    inference(definition_unfolding,[],[f70,f61])).
% 15.70/2.55  
% 15.70/2.55  fof(f83,plain,(
% 15.70/2.55    k7_mcart_1(sK4,sK5,sK6,sK8) != sK7),
% 15.70/2.55    inference(cnf_transformation,[],[f44])).
% 15.70/2.55  
% 15.70/2.55  cnf(c_34,negated_conjecture,
% 15.70/2.55      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 15.70/2.55      inference(cnf_transformation,[],[f100]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_602,plain,
% 15.70/2.55      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_13,plain,
% 15.70/2.55      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.70/2.55      inference(cnf_transformation,[],[f59]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_612,plain,
% 15.70/2.55      ( m1_subset_1(X0,X1) != iProver_top
% 15.70/2.55      | r2_hidden(X0,X1) = iProver_top
% 15.70/2.55      | v1_xboole_0(X1) = iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2233,plain,
% 15.70/2.55      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_602,c_612]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_7,plain,
% 15.70/2.55      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.70/2.55      | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f53]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_615,plain,
% 15.70/2.55      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 15.70/2.55      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2375,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2233,c_615]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_18,plain,
% 15.70/2.55      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f65]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_607,plain,
% 15.70/2.55      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_0,plain,
% 15.70/2.55      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.70/2.55      inference(cnf_transformation,[],[f45]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_622,plain,
% 15.70/2.55      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.55      | v1_xboole_0(X1) != iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_1851,plain,
% 15.70/2.55      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_607,c_622]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2507,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | k4_tarski(sK1(sK8),sK2(sK8)) = sK8 ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2375,c_1851]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3188,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8
% 15.70/2.55      | m1_subset_1(sK8,k1_xboole_0) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2507,c_602]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_32,negated_conjecture,
% 15.70/2.55      ( k1_xboole_0 != sK4 ),
% 15.70/2.55      inference(cnf_transformation,[],[f80]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_31,negated_conjecture,
% 15.70/2.55      ( k1_xboole_0 != sK5 ),
% 15.70/2.55      inference(cnf_transformation,[],[f81]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_30,negated_conjecture,
% 15.70/2.55      ( k1_xboole_0 != sK6 ),
% 15.70/2.55      inference(cnf_transformation,[],[f82]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_26,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = X1
% 15.70/2.55      | k1_xboole_0 = X0
% 15.70/2.55      | k1_xboole_0 = X2
% 15.70/2.55      | k1_xboole_0 = X3 ),
% 15.70/2.55      inference(cnf_transformation,[],[f98]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_41,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_26]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_25,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f111]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_42,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_25]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_274,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_683,plain,
% 15.70/2.55      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_274]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_684,plain,
% 15.70/2.55      ( sK6 != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = sK6
% 15.70/2.55      | k1_xboole_0 != k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_683]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_10,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = X1
% 15.70/2.55      | k1_xboole_0 = X0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f54]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_702,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,sK5) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = X0
% 15.70/2.55      | k1_xboole_0 = sK5 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_10]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_825,plain,
% 15.70/2.55      ( k2_zfmisc_1(sK4,sK5) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = sK5
% 15.70/2.55      | k1_xboole_0 = sK4 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_702]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3178,plain,
% 15.70/2.55      ( k2_zfmisc_1(sK4,sK5) = k1_xboole_0
% 15.70/2.55      | k4_tarski(sK1(sK8),sK2(sK8)) = sK8
% 15.70/2.55      | sK6 = k1_xboole_0 ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2507,c_10]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3439,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK8),sK2(sK8)) = sK8 ),
% 15.70/2.55      inference(global_propositional_subsumption,
% 15.70/2.55                [status(thm)],
% 15.70/2.55                [c_3188,c_32,c_31,c_30,c_41,c_42,c_684,c_825,c_3178]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_28,plain,
% 15.70/2.55      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f76]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3441,plain,
% 15.70/2.55      ( k1_mcart_1(sK8) = sK1(sK8) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3439,c_28]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_15,plain,
% 15.70/2.55      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.70/2.55      | r2_hidden(k1_mcart_1(X0),X1) ),
% 15.70/2.55      inference(cnf_transformation,[],[f63]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_610,plain,
% 15.70/2.55      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.70/2.55      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2377,plain,
% 15.70/2.55      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2233,c_610]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3508,plain,
% 15.70/2.55      ( r2_hidden(sK1(sK8),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_3441,c_2377]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_4187,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8)
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3508,c_615]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_14,plain,
% 15.70/2.55      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.70/2.55      | r2_hidden(k2_mcart_1(X0),X2) ),
% 15.70/2.55      inference(cnf_transformation,[],[f64]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_611,plain,
% 15.70/2.55      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.70/2.55      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2072,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 15.70/2.55      | r2_hidden(k2_mcart_1(sK3(k2_zfmisc_1(X0,X1))),X1) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_607,c_611]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3637,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 15.70/2.55      | v1_xboole_0(X1) != iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2072,c_622]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_5426,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = k1_xboole_0
% 15.70/2.55      | k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_4187,c_3637]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_6,plain,
% 15.70/2.55      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 15.70/2.55      inference(cnf_transformation,[],[f105]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_996,plain,
% 15.70/2.55      ( ~ r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,X0))
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = X0
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_6]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_1792,plain,
% 15.70/2.55      ( ~ r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK4,sK5)))
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK4,sK5)
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_996]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_1001,plain,
% 15.70/2.55      ( k2_zfmisc_1(sK4,sK5) != X0
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = k1_xboole_0
% 15.70/2.55      | k1_xboole_0 != X0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_274]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_1801,plain,
% 15.70/2.55      ( k2_zfmisc_1(sK4,sK5) != k2_zfmisc_1(sK4,sK5)
% 15.70/2.55      | k2_zfmisc_1(sK4,sK5) = k1_xboole_0
% 15.70/2.55      | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_1001]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_5428,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_4187,c_1851]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_4,plain,
% 15.70/2.55      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 15.70/2.55      inference(cnf_transformation,[],[f102]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_11115,plain,
% 15.70/2.55      ( r2_hidden(k2_zfmisc_1(sK4,sK5),k1_enumset1(k1_xboole_0,k1_xboole_0,k2_zfmisc_1(sK4,sK5))) ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_4]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_667,plain,
% 15.70/2.55      ( k2_zfmisc_1(X0,sK6) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = X0
% 15.70/2.55      | k1_xboole_0 = sK6 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_10]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_4823,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK6) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
% 15.70/2.55      | k1_xboole_0 = sK6 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_667]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_11300,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
% 15.70/2.55      | k1_xboole_0 = sK6 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_4823]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36222,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK1(sK8)),sK2(sK1(sK8))) = sK1(sK8) ),
% 15.70/2.55      inference(global_propositional_subsumption,
% 15.70/2.55                [status(thm)],
% 15.70/2.55                [c_5426,c_32,c_31,c_30,c_825,c_1792,c_1801,c_5428,
% 15.70/2.55                 c_11115,c_11300]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_33,negated_conjecture,
% 15.70/2.55      ( ~ m1_subset_1(X0,sK6)
% 15.70/2.55      | ~ m1_subset_1(X1,sK5)
% 15.70/2.55      | ~ m1_subset_1(X2,sK4)
% 15.70/2.55      | k4_tarski(k4_tarski(X2,X1),X0) != sK8
% 15.70/2.55      | sK7 = X0 ),
% 15.70/2.55      inference(cnf_transformation,[],[f99]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_603,plain,
% 15.70/2.55      ( k4_tarski(k4_tarski(X0,X1),X2) != sK8
% 15.70/2.55      | sK7 = X2
% 15.70/2.55      | m1_subset_1(X2,sK6) != iProver_top
% 15.70/2.55      | m1_subset_1(X1,sK5) != iProver_top
% 15.70/2.55      | m1_subset_1(X0,sK4) != iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36226,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK8),X0) != sK8
% 15.70/2.55      | sK7 = X0
% 15.70/2.55      | m1_subset_1(X0,sK6) != iProver_top
% 15.70/2.55      | m1_subset_1(sK2(sK1(sK8)),sK5) != iProver_top
% 15.70/2.55      | m1_subset_1(sK1(sK1(sK8)),sK4) != iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_36222,c_603]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36224,plain,
% 15.70/2.55      ( k1_mcart_1(sK1(sK8)) = sK1(sK1(sK8)) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_36222,c_28]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2513,plain,
% 15.70/2.55      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK4) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2377,c_610]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3932,plain,
% 15.70/2.55      ( r2_hidden(k1_mcart_1(sK1(sK8)),sK4) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(light_normalisation,[status(thm)],[c_2513,c_3441]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3936,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | r2_hidden(k1_mcart_1(sK1(sK8)),sK4) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3932,c_1851]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_12,plain,
% 15.70/2.55      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 15.70/2.55      inference(cnf_transformation,[],[f58]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_613,plain,
% 15.70/2.55      ( m1_subset_1(X0,X1) = iProver_top
% 15.70/2.55      | r2_hidden(X0,X1) != iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_4314,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(k1_mcart_1(sK1(sK8)),sK4) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3936,c_613]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36329,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(sK1(sK1(sK8)),sK4) = iProver_top ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_36224,c_4314]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_27,plain,
% 15.70/2.55      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 15.70/2.55      inference(cnf_transformation,[],[f77]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36225,plain,
% 15.70/2.55      ( k2_mcart_1(sK1(sK8)) = sK2(sK1(sK8)) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_36222,c_27]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2512,plain,
% 15.70/2.55      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2377,c_611]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3859,plain,
% 15.70/2.55      ( r2_hidden(k2_mcart_1(sK1(sK8)),sK5) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(light_normalisation,[status(thm)],[c_2512,c_3441]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3863,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | r2_hidden(k2_mcart_1(sK1(sK8)),sK5) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3859,c_1851]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_4258,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(k2_mcart_1(sK1(sK8)),sK5) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3863,c_613]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36372,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(sK2(sK1(sK8)),sK5) = iProver_top ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_36225,c_4258]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36415,plain,
% 15.70/2.55      ( k4_tarski(sK1(sK8),X0) != sK8
% 15.70/2.55      | sK7 = X0
% 15.70/2.55      | m1_subset_1(X0,sK6) != iProver_top ),
% 15.70/2.55      inference(global_propositional_subsumption,
% 15.70/2.55                [status(thm)],
% 15.70/2.55                [c_36226,c_32,c_31,c_30,c_825,c_1792,c_1801,c_11115,
% 15.70/2.55                 c_11300,c_36329,c_36372]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_36421,plain,
% 15.70/2.55      ( sK2(sK8) = sK7 | m1_subset_1(sK2(sK8),sK6) != iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3439,c_36415]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3442,plain,
% 15.70/2.55      ( k2_mcart_1(sK8) = sK2(sK8) ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_3439,c_27]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_19,plain,
% 15.70/2.55      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 15.70/2.55      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 15.70/2.55      | k1_xboole_0 = X2
% 15.70/2.55      | k1_xboole_0 = X1
% 15.70/2.55      | k1_xboole_0 = X3 ),
% 15.70/2.55      inference(cnf_transformation,[],[f91]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_606,plain,
% 15.70/2.55      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 15.70/2.55      | k1_xboole_0 = X0
% 15.70/2.55      | k1_xboole_0 = X1
% 15.70/2.55      | k1_xboole_0 = X2
% 15.70/2.55      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 15.70/2.55      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2192,plain,
% 15.70/2.55      ( k7_mcart_1(sK4,sK5,sK6,sK8) = k2_mcart_1(sK8)
% 15.70/2.55      | sK6 = k1_xboole_0
% 15.70/2.55      | sK5 = k1_xboole_0
% 15.70/2.55      | sK4 = k1_xboole_0 ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_602,c_606]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_718,plain,
% 15.70/2.55      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_274]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_719,plain,
% 15.70/2.55      ( sK5 != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = sK5
% 15.70/2.55      | k1_xboole_0 != k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_718]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_745,plain,
% 15.70/2.55      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_274]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_746,plain,
% 15.70/2.55      ( sK4 != k1_xboole_0
% 15.70/2.55      | k1_xboole_0 = sK4
% 15.70/2.55      | k1_xboole_0 != k1_xboole_0 ),
% 15.70/2.55      inference(instantiation,[status(thm)],[c_745]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2381,plain,
% 15.70/2.55      ( k7_mcart_1(sK4,sK5,sK6,sK8) = k2_mcart_1(sK8) ),
% 15.70/2.55      inference(global_propositional_subsumption,
% 15.70/2.55                [status(thm)],
% 15.70/2.55                [c_2192,c_32,c_31,c_30,c_41,c_42,c_684,c_719,c_746]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_29,negated_conjecture,
% 15.70/2.55      ( k7_mcart_1(sK4,sK5,sK6,sK8) != sK7 ),
% 15.70/2.55      inference(cnf_transformation,[],[f83]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2383,plain,
% 15.70/2.55      ( k2_mcart_1(sK8) != sK7 ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_2381,c_29]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3515,plain,
% 15.70/2.55      ( sK2(sK8) != sK7 ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_3442,c_2383]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2376,plain,
% 15.70/2.55      ( r2_hidden(k2_mcart_1(sK8),sK6) = iProver_top
% 15.70/2.55      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2233,c_611]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2432,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | r2_hidden(k2_mcart_1(sK8),sK6) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2376,c_1851]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_2578,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(k2_mcart_1(sK8),sK6) = iProver_top ),
% 15.70/2.55      inference(superposition,[status(thm)],[c_2432,c_613]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(c_3512,plain,
% 15.70/2.55      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 15.70/2.55      | m1_subset_1(sK2(sK8),sK6) = iProver_top ),
% 15.70/2.55      inference(demodulation,[status(thm)],[c_3442,c_2578]) ).
% 15.70/2.55  
% 15.70/2.55  cnf(contradiction,plain,
% 15.70/2.55      ( $false ),
% 15.70/2.55      inference(minisat,
% 15.70/2.55                [status(thm)],
% 15.70/2.55                [c_36421,c_11300,c_11115,c_3515,c_3512,c_1801,c_1792,
% 15.70/2.55                 c_825,c_30,c_31,c_32]) ).
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  % SZS output end CNFRefutation for theBenchmark.p
% 15.70/2.55  
% 15.70/2.55  ------                               Statistics
% 15.70/2.55  
% 15.70/2.55  ------ General
% 15.70/2.55  
% 15.70/2.55  abstr_ref_over_cycles:                  0
% 15.70/2.55  abstr_ref_under_cycles:                 0
% 15.70/2.55  gc_basic_clause_elim:                   0
% 15.70/2.55  forced_gc_time:                         0
% 15.70/2.55  parsing_time:                           0.012
% 15.70/2.55  unif_index_cands_time:                  0.
% 15.70/2.55  unif_index_add_time:                    0.
% 15.70/2.55  orderings_time:                         0.
% 15.70/2.55  out_proof_time:                         0.018
% 15.70/2.55  total_time:                             1.78
% 15.70/2.55  num_of_symbols:                         53
% 15.70/2.55  num_of_terms:                           71519
% 15.70/2.55  
% 15.70/2.55  ------ Preprocessing
% 15.70/2.55  
% 15.70/2.55  num_of_splits:                          0
% 15.70/2.55  num_of_split_atoms:                     0
% 15.70/2.55  num_of_reused_defs:                     0
% 15.70/2.55  num_eq_ax_congr_red:                    44
% 15.70/2.55  num_of_sem_filtered_clauses:            1
% 15.70/2.55  num_of_subtypes:                        0
% 15.70/2.55  monotx_restored_types:                  0
% 15.70/2.55  sat_num_of_epr_types:                   0
% 15.70/2.55  sat_num_of_non_cyclic_types:            0
% 15.70/2.55  sat_guarded_non_collapsed_types:        0
% 15.70/2.55  num_pure_diseq_elim:                    0
% 15.70/2.55  simp_replaced_by:                       0
% 15.70/2.55  res_preprocessed:                       124
% 15.70/2.55  prep_upred:                             0
% 15.70/2.55  prep_unflattend:                        0
% 15.70/2.55  smt_new_axioms:                         0
% 15.70/2.55  pred_elim_cands:                        3
% 15.70/2.55  pred_elim:                              0
% 15.70/2.55  pred_elim_cl:                           0
% 15.70/2.55  pred_elim_cycles:                       1
% 15.70/2.55  merged_defs:                            0
% 15.70/2.55  merged_defs_ncl:                        0
% 15.70/2.55  bin_hyper_res:                          0
% 15.70/2.55  prep_cycles:                            3
% 15.70/2.55  pred_elim_time:                         0.
% 15.70/2.55  splitting_time:                         0.
% 15.70/2.55  sem_filter_time:                        0.
% 15.70/2.55  monotx_time:                            0.
% 15.70/2.55  subtype_inf_time:                       0.
% 15.70/2.55  
% 15.70/2.55  ------ Problem properties
% 15.70/2.55  
% 15.70/2.55  clauses:                                35
% 15.70/2.55  conjectures:                            6
% 15.70/2.55  epr:                                    6
% 15.70/2.55  horn:                                   26
% 15.70/2.55  ground:                                 5
% 15.70/2.55  unary:                                  16
% 15.70/2.55  binary:                                 6
% 15.70/2.55  lits:                                   78
% 15.70/2.55  lits_eq:                                49
% 15.70/2.55  fd_pure:                                0
% 15.70/2.55  fd_pseudo:                              0
% 15.70/2.55  fd_cond:                                9
% 15.70/2.55  fd_pseudo_cond:                         3
% 15.70/2.55  ac_symbols:                             0
% 15.70/2.55  
% 15.70/2.55  ------ Propositional Solver
% 15.70/2.55  
% 15.70/2.55  prop_solver_calls:                      29
% 15.70/2.55  prop_fast_solver_calls:                 3699
% 15.70/2.55  smt_solver_calls:                       0
% 15.70/2.55  smt_fast_solver_calls:                  0
% 15.70/2.55  prop_num_of_clauses:                    24247
% 15.70/2.55  prop_preprocess_simplified:             40564
% 15.70/2.55  prop_fo_subsumed:                       136
% 15.70/2.55  prop_solver_time:                       0.
% 15.70/2.55  smt_solver_time:                        0.
% 15.70/2.55  smt_fast_solver_time:                   0.
% 15.70/2.55  prop_fast_solver_time:                  0.
% 15.70/2.55  prop_unsat_core_time:                   0.002
% 15.70/2.55  
% 15.70/2.55  ------ QBF
% 15.70/2.55  
% 15.70/2.55  qbf_q_res:                              0
% 15.70/2.55  qbf_num_tautologies:                    0
% 15.70/2.55  qbf_prep_cycles:                        0
% 15.70/2.55  
% 15.70/2.55  ------ BMC1
% 15.70/2.55  
% 15.70/2.55  bmc1_current_bound:                     -1
% 15.70/2.55  bmc1_last_solved_bound:                 -1
% 15.70/2.55  bmc1_unsat_core_size:                   -1
% 15.70/2.55  bmc1_unsat_core_parents_size:           -1
% 15.70/2.55  bmc1_merge_next_fun:                    0
% 15.70/2.55  bmc1_unsat_core_clauses_time:           0.
% 15.70/2.55  
% 15.70/2.55  ------ Instantiation
% 15.70/2.55  
% 15.70/2.55  inst_num_of_clauses:                    7669
% 15.70/2.55  inst_num_in_passive:                    3166
% 15.70/2.55  inst_num_in_active:                     2246
% 15.70/2.55  inst_num_in_unprocessed:                2257
% 15.70/2.55  inst_num_of_loops:                      2260
% 15.70/2.55  inst_num_of_learning_restarts:          0
% 15.70/2.55  inst_num_moves_active_passive:          14
% 15.70/2.55  inst_lit_activity:                      0
% 15.70/2.55  inst_lit_activity_moves:                0
% 15.70/2.55  inst_num_tautologies:                   0
% 15.70/2.55  inst_num_prop_implied:                  0
% 15.70/2.55  inst_num_existing_simplified:           0
% 15.70/2.55  inst_num_eq_res_simplified:             0
% 15.70/2.55  inst_num_child_elim:                    0
% 15.70/2.55  inst_num_of_dismatching_blockings:      1983
% 15.70/2.55  inst_num_of_non_proper_insts:           4961
% 15.70/2.55  inst_num_of_duplicates:                 0
% 15.70/2.55  inst_inst_num_from_inst_to_res:         0
% 15.70/2.55  inst_dismatching_checking_time:         0.
% 15.70/2.55  
% 15.70/2.55  ------ Resolution
% 15.70/2.55  
% 15.70/2.55  res_num_of_clauses:                     0
% 15.70/2.55  res_num_in_passive:                     0
% 15.70/2.55  res_num_in_active:                      0
% 15.70/2.55  res_num_of_loops:                       127
% 15.70/2.55  res_forward_subset_subsumed:            46
% 15.70/2.55  res_backward_subset_subsumed:           0
% 15.70/2.55  res_forward_subsumed:                   0
% 15.70/2.55  res_backward_subsumed:                  0
% 15.70/2.55  res_forward_subsumption_resolution:     0
% 15.70/2.55  res_backward_subsumption_resolution:    0
% 15.70/2.55  res_clause_to_clause_subsumption:       7068
% 15.70/2.55  res_orphan_elimination:                 0
% 15.70/2.55  res_tautology_del:                      1
% 15.70/2.55  res_num_eq_res_simplified:              0
% 15.70/2.55  res_num_sel_changes:                    0
% 15.70/2.55  res_moves_from_active_to_pass:          0
% 15.70/2.55  
% 15.70/2.55  ------ Superposition
% 15.70/2.55  
% 15.70/2.55  sup_time_total:                         0.
% 15.70/2.55  sup_time_generating:                    0.
% 15.70/2.55  sup_time_sim_full:                      0.
% 15.70/2.55  sup_time_sim_immed:                     0.
% 15.70/2.55  
% 15.70/2.55  sup_num_of_clauses:                     2433
% 15.70/2.55  sup_num_in_active:                      406
% 15.70/2.55  sup_num_in_passive:                     2027
% 15.70/2.55  sup_num_of_loops:                       450
% 15.70/2.55  sup_fw_superposition:                   2424
% 15.70/2.55  sup_bw_superposition:                   1075
% 15.70/2.55  sup_immediate_simplified:               777
% 15.70/2.55  sup_given_eliminated:                   0
% 15.70/2.55  comparisons_done:                       0
% 15.70/2.55  comparisons_avoided:                    6661
% 15.70/2.55  
% 15.70/2.55  ------ Simplifications
% 15.70/2.55  
% 15.70/2.55  
% 15.70/2.55  sim_fw_subset_subsumed:                 121
% 15.70/2.55  sim_bw_subset_subsumed:                 18
% 15.70/2.55  sim_fw_subsumed:                        75
% 15.70/2.55  sim_bw_subsumed:                        10
% 15.70/2.55  sim_fw_subsumption_res:                 0
% 15.70/2.55  sim_bw_subsumption_res:                 0
% 15.70/2.55  sim_tautology_del:                      1
% 15.70/2.55  sim_eq_tautology_del:                   605
% 15.70/2.55  sim_eq_res_simp:                        9
% 15.70/2.55  sim_fw_demodulated:                     589
% 15.70/2.55  sim_bw_demodulated:                     33
% 15.70/2.55  sim_light_normalised:                   188
% 15.70/2.55  sim_joinable_taut:                      0
% 15.70/2.55  sim_joinable_simp:                      0
% 15.70/2.55  sim_ac_normalised:                      0
% 15.70/2.55  sim_smt_subsumption:                    0
% 15.70/2.55  
%------------------------------------------------------------------------------
