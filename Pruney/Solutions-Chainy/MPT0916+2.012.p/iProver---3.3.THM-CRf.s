%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:13 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1414)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3) )
        & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
              & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                  & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f32,f31,f30,f29])).

fof(f54,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f56,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1243,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1248,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3509,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1243,c_1248])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1247,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2353,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1243,c_1247])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1246,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1744,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1243,c_1246])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1245,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2119,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1245])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1416,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1417,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_1501,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1505,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1501])).

cnf(c_2194,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2119,c_26,c_1417,c_1505])).

cnf(c_2195,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2194])).

cnf(c_2713,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_2195])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1502,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1503,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_3190,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_26,c_1417,c_1503])).

cnf(c_3191,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3190])).

cnf(c_3956,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3509,c_3191])).

cnf(c_1413,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3957,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3956])).

cnf(c_6916,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3956,c_26,c_1414])).

cnf(c_6917,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6916])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1242,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6929,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6917,c_1242])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_50,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_53,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_57,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1462,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1466,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2319,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2326,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_1244,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1250,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3716,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1250])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1851,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1251])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1258,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3836,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_1258])).

cnf(c_5094,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_3836])).

cnf(c_6921,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6917,c_5094])).

cnf(c_6970,plain,
    ( r2_hidden(k2_mcart_1(sK7),k1_xboole_0)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6921])).

cnf(c_6977,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6929,c_51,c_54,c_58,c_1467,c_2327,c_6921])).

cnf(c_6978,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6977])).

cnf(c_6986,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6978,c_1245])).

cnf(c_49,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_52,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_54,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_56,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_58,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_1465,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_1467,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_1621,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1622,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) = iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1621])).

cnf(c_1624,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3796,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3802,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3796])).

cnf(c_3804,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3802])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1241,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1852,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1251])).

cnf(c_6985,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6978,c_1852])).

cnf(c_7235,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6986,c_26,c_51,c_54,c_58,c_1417,c_1467,c_1503,c_1624,c_3804,c_6985])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1240,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1853,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1251])).

cnf(c_7243,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7235,c_1853])).

cnf(c_3768,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3774,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3768])).

cnf(c_3776,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3774])).

cnf(c_1611,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1612,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_1614,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7243,c_3776,c_1614,c_1505,c_1467,c_1417,c_58,c_54,c_51,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:51:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.81/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/0.99  
% 2.81/0.99  ------  iProver source info
% 2.81/0.99  
% 2.81/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.81/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/0.99  git: non_committed_changes: false
% 2.81/0.99  git: last_make_outside_of_git: false
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     num_symb
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       true
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  ------ Parsing...
% 2.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/0.99  ------ Proving...
% 2.81/0.99  ------ Problem Properties 
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  clauses                                 22
% 2.81/0.99  conjectures                             6
% 2.81/0.99  EPR                                     5
% 2.81/0.99  Horn                                    18
% 2.81/0.99  unary                                   6
% 2.81/0.99  binary                                  10
% 2.81/0.99  lits                                    50
% 2.81/0.99  lits eq                                 12
% 2.81/0.99  fd_pure                                 0
% 2.81/0.99  fd_pseudo                               0
% 2.81/0.99  fd_cond                                 3
% 2.81/0.99  fd_pseudo_cond                          0
% 2.81/0.99  AC symbols                              0
% 2.81/0.99  
% 2.81/0.99  ------ Schedule dynamic 5 is on 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  Current options:
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     none
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       false
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ Proving...
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS status Theorem for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  fof(f11,conjecture,(
% 2.81/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f12,negated_conjecture,(
% 2.81/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.81/0.99    inference(negated_conjecture,[],[f11])).
% 2.81/0.99  
% 2.81/0.99  fof(f22,plain,(
% 2.81/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f12])).
% 2.81/0.99  
% 2.81/0.99  fof(f23,plain,(
% 2.81/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.81/0.99    inference(flattening,[],[f22])).
% 2.81/0.99  
% 2.81/0.99  fof(f32,plain,(
% 2.81/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f31,plain,(
% 2.81/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f30,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f29,plain,(
% 2.81/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f33,plain,(
% 2.81/0.99    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f32,f31,f30,f29])).
% 2.81/0.99  
% 2.81/0.99  fof(f54,plain,(
% 2.81/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f8,axiom,(
% 2.81/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f45,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f8])).
% 2.81/0.99  
% 2.81/0.99  fof(f61,plain,(
% 2.81/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.81/0.99    inference(definition_unfolding,[],[f54,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f10,axiom,(
% 2.81/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f21,plain,(
% 2.81/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.81/0.99    inference(ennf_transformation,[],[f10])).
% 2.81/0.99  
% 2.81/0.99  fof(f50,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(cnf_transformation,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f57,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(definition_unfolding,[],[f50,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f49,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(cnf_transformation,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f58,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(definition_unfolding,[],[f49,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f48,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(cnf_transformation,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f59,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.81/0.99    inference(definition_unfolding,[],[f48,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f56,plain,(
% 2.81/0.99    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f55,plain,(
% 2.81/0.99    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f60,plain,(
% 2.81/0.99    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.81/0.99    inference(definition_unfolding,[],[f55,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f9,axiom,(
% 2.81/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f20,plain,(
% 2.81/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.81/0.99    inference(ennf_transformation,[],[f9])).
% 2.81/0.99  
% 2.81/0.99  fof(f46,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f20])).
% 2.81/0.99  
% 2.81/0.99  fof(f47,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f20])).
% 2.81/0.99  
% 2.81/0.99  fof(f53,plain,(
% 2.81/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f6,axiom,(
% 2.81/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f18,plain,(
% 2.81/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.81/0.99    inference(ennf_transformation,[],[f6])).
% 2.81/0.99  
% 2.81/0.99  fof(f19,plain,(
% 2.81/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.81/0.99    inference(flattening,[],[f18])).
% 2.81/0.99  
% 2.81/0.99  fof(f42,plain,(
% 2.81/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f19])).
% 2.81/0.99  
% 2.81/0.99  fof(f5,axiom,(
% 2.81/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f41,plain,(
% 2.81/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f5])).
% 2.81/0.99  
% 2.81/0.99  fof(f4,axiom,(
% 2.81/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f17,plain,(
% 2.81/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.81/0.99    inference(ennf_transformation,[],[f4])).
% 2.81/0.99  
% 2.81/0.99  fof(f40,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f17])).
% 2.81/0.99  
% 2.81/0.99  fof(f1,axiom,(
% 2.81/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f13,plain,(
% 2.81/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.81/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.81/0.99  
% 2.81/0.99  fof(f14,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f13])).
% 2.81/0.99  
% 2.81/0.99  fof(f34,plain,(
% 2.81/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f14])).
% 2.81/0.99  
% 2.81/0.99  fof(f7,axiom,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f28,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.81/0.99    inference(nnf_transformation,[],[f7])).
% 2.81/0.99  
% 2.81/0.99  fof(f43,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f28])).
% 2.81/0.99  
% 2.81/0.99  fof(f2,axiom,(
% 2.81/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.81/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f15,plain,(
% 2.81/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f2])).
% 2.81/0.99  
% 2.81/0.99  fof(f24,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(nnf_transformation,[],[f15])).
% 2.81/0.99  
% 2.81/0.99  fof(f25,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(rectify,[],[f24])).
% 2.81/0.99  
% 2.81/0.99  fof(f26,plain,(
% 2.81/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f27,plain,(
% 2.81/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.81/0.99  
% 2.81/0.99  fof(f35,plain,(
% 2.81/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f52,plain,(
% 2.81/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f51,plain,(
% 2.81/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.81/0.99    inference(cnf_transformation,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  cnf(c_18,negated_conjecture,
% 2.81/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1243,plain,
% 2.81/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_13,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.81/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.81/0.99      | k1_xboole_0 = X3
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X1 ),
% 2.81/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1248,plain,
% 2.81/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X0
% 2.81/0.99      | k1_xboole_0 = X1
% 2.81/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3509,plain,
% 2.81/0.99      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.81/0.99      | sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0 ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_1243,c_1248]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_14,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.81/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.81/0.99      | k1_xboole_0 = X3
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X1 ),
% 2.81/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1247,plain,
% 2.81/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X0
% 2.81/0.99      | k1_xboole_0 = X1
% 2.81/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2353,plain,
% 2.81/0.99      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.81/0.99      | sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0 ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_1243,c_1247]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_15,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.81/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.81/0.99      | k1_xboole_0 = X3
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X1 ),
% 2.81/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1246,plain,
% 2.81/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.81/0.99      | k1_xboole_0 = X2
% 2.81/0.99      | k1_xboole_0 = X0
% 2.81/0.99      | k1_xboole_0 = X1
% 2.81/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1744,plain,
% 2.81/0.99      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.81/0.99      | sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0 ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_1243,c_1246]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_16,negated_conjecture,
% 2.81/0.99      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.81/0.99      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.81/0.99      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.81/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1245,plain,
% 2.81/0.99      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.81/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.81/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2119,plain,
% 2.81/0.99      ( sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0
% 2.81/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.81/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.81/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_1744,c_1245]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_17,negated_conjecture,
% 2.81/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_26,plain,
% 2.81/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_12,plain,
% 2.81/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.81/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1416,plain,
% 2.81/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.81/0.99      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1417,plain,
% 2.81/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.81/0.99      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1501,plain,
% 2.81/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.81/0.99      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1505,plain,
% 2.81/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.81/0.99      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1501]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2194,plain,
% 2.81/0.99      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.81/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.81/0.99      | sK1 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK3 = k1_xboole_0 ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_2119,c_26,c_1417,c_1505]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2195,plain,
% 2.81/0.99      ( sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0
% 2.81/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.81/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_2194]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2713,plain,
% 2.81/0.99      ( sK3 = k1_xboole_0
% 2.81/0.99      | sK2 = k1_xboole_0
% 2.81/0.99      | sK1 = k1_xboole_0
% 2.81/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.81/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2353,c_2195]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_11,plain,
% 2.81/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.81/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1502,plain,
% 2.81/0.99      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.81/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1503,plain,
% 2.81/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.81/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3190,plain,
% 2.81/1.00      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.81/1.00      | sK1 = k1_xboole_0
% 2.81/1.00      | sK2 = k1_xboole_0
% 2.81/1.00      | sK3 = k1_xboole_0 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2713,c_26,c_1417,c_1503]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3191,plain,
% 2.81/1.00      ( sK3 = k1_xboole_0
% 2.81/1.00      | sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0
% 2.81/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_3190]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3956,plain,
% 2.81/1.00      ( sK3 = k1_xboole_0
% 2.81/1.00      | sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0
% 2.81/1.00      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_3509,c_3191]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1413,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.81/1.00      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3957,plain,
% 2.81/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.81/1.00      | sK3 = k1_xboole_0
% 2.81/1.00      | sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0 ),
% 2.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3956]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6916,plain,
% 2.81/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_3956,c_26,c_1414]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6917,plain,
% 2.81/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_6916]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_19,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1242,plain,
% 2.81/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6929,plain,
% 2.81/1.00      ( sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0
% 2.81/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_6917,c_1242]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_8,plain,
% 2.81/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_50,plain,
% 2.81/1.00      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.81/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.81/1.00      | v1_xboole_0(k1_xboole_0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_7,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_53,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5,plain,
% 2.81/1.00      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_57,plain,
% 2.81/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.81/1.00      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1462,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1466,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_0,plain,
% 2.81/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2319,plain,
% 2.81/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),X0) | ~ v1_xboole_0(X0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2326,plain,
% 2.81/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),k1_xboole_0)
% 2.81/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_2319]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1244,plain,
% 2.81/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1250,plain,
% 2.81/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.81/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3716,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1244,c_1250]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_10,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1251,plain,
% 2.81/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.81/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1851,plain,
% 2.81/1.00      ( r1_tarski(sK6,sK3) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1242,c_1251]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3,plain,
% 2.81/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1258,plain,
% 2.81/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.81/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.81/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3836,plain,
% 2.81/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 2.81/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1851,c_1258]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5094,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(sK7),sK3) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_3716,c_3836]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6921,plain,
% 2.81/1.00      ( sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0
% 2.81/1.00      | r2_hidden(k2_mcart_1(sK7),k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_6917,c_5094]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6970,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(sK7),k1_xboole_0)
% 2.81/1.00      | sK2 = k1_xboole_0
% 2.81/1.00      | sK1 = k1_xboole_0 ),
% 2.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6921]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6977,plain,
% 2.81/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_6929,c_51,c_54,c_58,c_1467,c_2327,c_6921]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6978,plain,
% 2.81/1.00      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_6977]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6986,plain,
% 2.81/1.00      ( sK1 = k1_xboole_0
% 2.81/1.00      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.81/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.81/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_6978,c_1245]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_49,plain,
% 2.81/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.81/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.81/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_51,plain,
% 2.81/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.81/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.81/1.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_49]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_52,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_54,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_52]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_56,plain,
% 2.81/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 2.81/1.00      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_58,plain,
% 2.81/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
% 2.81/1.00      | r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_56]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1465,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1467,plain,
% 2.81/1.00      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1465]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1621,plain,
% 2.81/1.00      ( ~ r1_tarski(sK5,X0)
% 2.81/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0)
% 2.81/1.00      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1622,plain,
% 2.81/1.00      ( r1_tarski(sK5,X0) != iProver_top
% 2.81/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) = iProver_top
% 2.81/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1621]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1624,plain,
% 2.81/1.00      ( r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.81/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.81/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3796,plain,
% 2.81/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) | ~ v1_xboole_0(X0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3802,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top
% 2.81/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_3796]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3804,plain,
% 2.81/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) != iProver_top
% 2.81/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3802]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_20,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1241,plain,
% 2.81/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1852,plain,
% 2.81/1.00      ( r1_tarski(sK5,sK2) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1241,c_1251]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6985,plain,
% 2.81/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_6978,c_1852]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_7235,plain,
% 2.81/1.00      ( sK1 = k1_xboole_0 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_6986,c_26,c_51,c_54,c_58,c_1417,c_1467,c_1503,c_1624,
% 2.81/1.00                 c_3804,c_6985]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_21,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1240,plain,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1853,plain,
% 2.81/1.00      ( r1_tarski(sK4,sK1) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1240,c_1251]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_7243,plain,
% 2.81/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_7235,c_1853]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3768,plain,
% 2.81/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0) | ~ v1_xboole_0(X0) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3774,plain,
% 2.81/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top
% 2.81/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_3768]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3776,plain,
% 2.81/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) != iProver_top
% 2.81/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3774]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1611,plain,
% 2.81/1.00      ( ~ r1_tarski(sK4,X0)
% 2.81/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0)
% 2.81/1.00      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1612,plain,
% 2.81/1.00      ( r1_tarski(sK4,X0) != iProver_top
% 2.81/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0) = iProver_top
% 2.81/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1611]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1614,plain,
% 2.81/1.00      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.81/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.81/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),k1_xboole_0) = iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1612]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(contradiction,plain,
% 2.81/1.00      ( $false ),
% 2.81/1.00      inference(minisat,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_7243,c_3776,c_1614,c_1505,c_1467,c_1417,c_58,c_54,
% 2.81/1.00                 c_51,c_26]) ).
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  ------                               Statistics
% 2.81/1.00  
% 2.81/1.00  ------ General
% 2.81/1.00  
% 2.81/1.00  abstr_ref_over_cycles:                  0
% 2.81/1.00  abstr_ref_under_cycles:                 0
% 2.81/1.00  gc_basic_clause_elim:                   0
% 2.81/1.00  forced_gc_time:                         0
% 2.81/1.00  parsing_time:                           0.009
% 2.81/1.00  unif_index_cands_time:                  0.
% 2.81/1.00  unif_index_add_time:                    0.
% 2.81/1.00  orderings_time:                         0.
% 2.81/1.00  out_proof_time:                         0.008
% 2.81/1.00  total_time:                             0.233
% 2.81/1.00  num_of_symbols:                         53
% 2.81/1.00  num_of_terms:                           8489
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing
% 2.81/1.00  
% 2.81/1.00  num_of_splits:                          0
% 2.81/1.00  num_of_split_atoms:                     0
% 2.81/1.00  num_of_reused_defs:                     0
% 2.81/1.00  num_eq_ax_congr_red:                    14
% 2.81/1.00  num_of_sem_filtered_clauses:            1
% 2.81/1.00  num_of_subtypes:                        0
% 2.81/1.00  monotx_restored_types:                  0
% 2.81/1.00  sat_num_of_epr_types:                   0
% 2.81/1.00  sat_num_of_non_cyclic_types:            0
% 2.81/1.00  sat_guarded_non_collapsed_types:        0
% 2.81/1.00  num_pure_diseq_elim:                    0
% 2.81/1.00  simp_replaced_by:                       0
% 2.81/1.00  res_preprocessed:                       91
% 2.81/1.00  prep_upred:                             0
% 2.81/1.00  prep_unflattend:                        20
% 2.81/1.00  smt_new_axioms:                         0
% 2.81/1.00  pred_elim_cands:                        5
% 2.81/1.00  pred_elim:                              0
% 2.81/1.00  pred_elim_cl:                           0
% 2.81/1.00  pred_elim_cycles:                       2
% 2.81/1.00  merged_defs:                            6
% 2.81/1.00  merged_defs_ncl:                        0
% 2.81/1.00  bin_hyper_res:                          6
% 2.81/1.00  prep_cycles:                            3
% 2.81/1.00  pred_elim_time:                         0.013
% 2.81/1.00  splitting_time:                         0.
% 2.81/1.00  sem_filter_time:                        0.
% 2.81/1.00  monotx_time:                            0.001
% 2.81/1.00  subtype_inf_time:                       0.
% 2.81/1.00  
% 2.81/1.00  ------ Problem properties
% 2.81/1.00  
% 2.81/1.00  clauses:                                22
% 2.81/1.00  conjectures:                            6
% 2.81/1.00  epr:                                    5
% 2.81/1.00  horn:                                   18
% 2.81/1.00  ground:                                 6
% 2.81/1.00  unary:                                  6
% 2.81/1.00  binary:                                 10
% 2.81/1.00  lits:                                   50
% 2.81/1.00  lits_eq:                                12
% 2.81/1.00  fd_pure:                                0
% 2.81/1.00  fd_pseudo:                              0
% 2.81/1.00  fd_cond:                                3
% 2.81/1.00  fd_pseudo_cond:                         0
% 2.81/1.00  ac_symbols:                             0
% 2.81/1.00  
% 2.81/1.00  ------ Propositional Solver
% 2.81/1.00  
% 2.81/1.00  prop_solver_calls:                      24
% 2.81/1.00  prop_fast_solver_calls:                 688
% 2.81/1.00  smt_solver_calls:                       0
% 2.81/1.00  smt_fast_solver_calls:                  0
% 2.81/1.00  prop_num_of_clauses:                    2558
% 2.81/1.00  prop_preprocess_simplified:             7598
% 2.81/1.00  prop_fo_subsumed:                       10
% 2.81/1.00  prop_solver_time:                       0.
% 2.81/1.00  smt_solver_time:                        0.
% 2.81/1.00  smt_fast_solver_time:                   0.
% 2.81/1.00  prop_fast_solver_time:                  0.
% 2.81/1.00  prop_unsat_core_time:                   0.
% 2.81/1.00  
% 2.81/1.00  ------ QBF
% 2.81/1.00  
% 2.81/1.00  qbf_q_res:                              0
% 2.81/1.00  qbf_num_tautologies:                    0
% 2.81/1.00  qbf_prep_cycles:                        0
% 2.81/1.00  
% 2.81/1.00  ------ BMC1
% 2.81/1.00  
% 2.81/1.00  bmc1_current_bound:                     -1
% 2.81/1.00  bmc1_last_solved_bound:                 -1
% 2.81/1.00  bmc1_unsat_core_size:                   -1
% 2.81/1.00  bmc1_unsat_core_parents_size:           -1
% 2.81/1.00  bmc1_merge_next_fun:                    0
% 2.81/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation
% 2.81/1.00  
% 2.81/1.00  inst_num_of_clauses:                    740
% 2.81/1.00  inst_num_in_passive:                    372
% 2.81/1.00  inst_num_in_active:                     250
% 2.81/1.00  inst_num_in_unprocessed:                118
% 2.81/1.00  inst_num_of_loops:                      290
% 2.81/1.00  inst_num_of_learning_restarts:          0
% 2.81/1.00  inst_num_moves_active_passive:          38
% 2.81/1.00  inst_lit_activity:                      0
% 2.81/1.00  inst_lit_activity_moves:                0
% 2.81/1.00  inst_num_tautologies:                   0
% 2.81/1.00  inst_num_prop_implied:                  0
% 2.81/1.00  inst_num_existing_simplified:           0
% 2.81/1.00  inst_num_eq_res_simplified:             0
% 2.81/1.00  inst_num_child_elim:                    0
% 2.81/1.00  inst_num_of_dismatching_blockings:      106
% 2.81/1.00  inst_num_of_non_proper_insts:           539
% 2.81/1.00  inst_num_of_duplicates:                 0
% 2.81/1.00  inst_inst_num_from_inst_to_res:         0
% 2.81/1.00  inst_dismatching_checking_time:         0.
% 2.81/1.00  
% 2.81/1.00  ------ Resolution
% 2.81/1.00  
% 2.81/1.00  res_num_of_clauses:                     0
% 2.81/1.00  res_num_in_passive:                     0
% 2.81/1.00  res_num_in_active:                      0
% 2.81/1.00  res_num_of_loops:                       94
% 2.81/1.00  res_forward_subset_subsumed:            10
% 2.81/1.00  res_backward_subset_subsumed:           0
% 2.81/1.00  res_forward_subsumed:                   0
% 2.81/1.00  res_backward_subsumed:                  0
% 2.81/1.00  res_forward_subsumption_resolution:     0
% 2.81/1.00  res_backward_subsumption_resolution:    0
% 2.81/1.00  res_clause_to_clause_subsumption:       141
% 2.81/1.00  res_orphan_elimination:                 0
% 2.81/1.00  res_tautology_del:                      28
% 2.81/1.00  res_num_eq_res_simplified:              0
% 2.81/1.00  res_num_sel_changes:                    0
% 2.81/1.00  res_moves_from_active_to_pass:          0
% 2.81/1.00  
% 2.81/1.00  ------ Superposition
% 2.81/1.00  
% 2.81/1.00  sup_time_total:                         0.
% 2.81/1.00  sup_time_generating:                    0.
% 2.81/1.00  sup_time_sim_full:                      0.
% 2.81/1.00  sup_time_sim_immed:                     0.
% 2.81/1.00  
% 2.81/1.00  sup_num_of_clauses:                     71
% 2.81/1.00  sup_num_in_active:                      45
% 2.81/1.00  sup_num_in_passive:                     26
% 2.81/1.00  sup_num_of_loops:                       56
% 2.81/1.00  sup_fw_superposition:                   37
% 2.81/1.00  sup_bw_superposition:                   42
% 2.81/1.00  sup_immediate_simplified:               7
% 2.81/1.00  sup_given_eliminated:                   0
% 2.81/1.00  comparisons_done:                       0
% 2.81/1.00  comparisons_avoided:                    36
% 2.81/1.00  
% 2.81/1.00  ------ Simplifications
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  sim_fw_subset_subsumed:                 6
% 2.81/1.00  sim_bw_subset_subsumed:                 11
% 2.81/1.00  sim_fw_subsumed:                        1
% 2.81/1.00  sim_bw_subsumed:                        0
% 2.81/1.00  sim_fw_subsumption_res:                 0
% 2.81/1.00  sim_bw_subsumption_res:                 0
% 2.81/1.00  sim_tautology_del:                      3
% 2.81/1.00  sim_eq_tautology_del:                   3
% 2.81/1.00  sim_eq_res_simp:                        0
% 2.81/1.00  sim_fw_demodulated:                     0
% 2.81/1.00  sim_bw_demodulated:                     9
% 2.81/1.00  sim_light_normalised:                   0
% 2.81/1.00  sim_joinable_taut:                      0
% 2.81/1.00  sim_joinable_simp:                      0
% 2.81/1.00  sim_ac_normalised:                      0
% 2.81/1.00  sim_smt_subsumption:                    0
% 2.81/1.00  
%------------------------------------------------------------------------------
