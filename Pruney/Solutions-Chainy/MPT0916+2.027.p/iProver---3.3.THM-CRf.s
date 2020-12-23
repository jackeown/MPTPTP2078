%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:16 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 935 expanded)
%              Number of clauses        :   84 ( 313 expanded)
%              Number of leaves         :   16 ( 277 expanded)
%              Depth                    :   22
%              Number of atoms          :  423 (4640 expanded)
%              Number of equality atoms :  182 ( 549 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f26,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f25,f24,f23,f22])).

fof(f42,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f42,f33])).

fof(f7,axiom,(
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

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f43,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f43,f33])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f44,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_834,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_839,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3055,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_834,c_839])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_838,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3138,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_834,c_838])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_42,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_199,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_200,plain,
    ( r1_tarski(sK6,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_202,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_520,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_543,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_980,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_524,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1298,plain,
    ( X0 != sK3
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1303,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1027,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),X0)
    | ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r1_xboole_0(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2199,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r1_xboole_0(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_521,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2270,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_2271,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X3,X1)
    | r1_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1232,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK6,X2)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3325,plain,
    ( ~ r1_tarski(sK6,X0)
    | ~ r1_tarski(sK6,X1)
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_3327,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0)
    | r1_xboole_0(sK6,sK6)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3325])).

cnf(c_3434,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_12,c_42,c_202,c_543,c_980,c_1303,c_2199,c_2271,c_3327])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_837,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3131,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_834,c_837])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_836,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3260,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3131,c_836])).

cnf(c_21,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_983,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_984,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_1046,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1050,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_3440,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3260,c_12,c_21,c_42,c_202,c_543,c_980,c_984,c_1050,c_1303,c_2199,c_2271,c_3327])).

cnf(c_3441,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3440])).

cnf(c_3448,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_3441])).

cnf(c_1047,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1048,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_10337,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3448,c_21,c_984,c_1048])).

cnf(c_10338,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_10337])).

cnf(c_10344,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3055,c_10338])).

cnf(c_981,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_10347,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10344,c_12,c_21,c_42,c_202,c_543,c_980,c_981,c_1303,c_2199,c_2271,c_3327])).

cnf(c_10348,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10347])).

cnf(c_10361,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10348,c_836])).

cnf(c_41,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_43,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_832,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_842,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1139,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_842])).

cnf(c_844,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_xboole_0(X3,X1) != iProver_top
    | r1_xboole_0(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3020,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,sK5) = iProver_top
    | r1_xboole_0(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_844])).

cnf(c_6160,plain,
    ( r1_xboole_0(sK5,sK5) = iProver_top
    | r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_3020])).

cnf(c_1201,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ r1_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2919,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ r1_xboole_0(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_2920,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | r1_xboole_0(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_7461,plain,
    ( r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_21,c_984,c_1048,c_2920])).

cnf(c_10353,plain,
    ( sK1 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10348,c_7461])).

cnf(c_10698,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10361,c_43,c_10353])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_831,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1140,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_842])).

cnf(c_3021,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,sK4) = iProver_top
    | r1_xboole_0(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_844])).

cnf(c_8755,plain,
    ( r1_xboole_0(sK4,sK4) = iProver_top
    | r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_3021])).

cnf(c_1191,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r1_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2916,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r1_xboole_0(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_2917,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | r1_xboole_0(sK4,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_10331,plain,
    ( r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8755,c_21,c_984,c_1050,c_2917])).

cnf(c_10701,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10698,c_10331])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10701,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.16/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.06  
% 2.16/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.06  
% 2.16/1.06  ------  iProver source info
% 2.16/1.06  
% 2.16/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.06  git: non_committed_changes: false
% 2.16/1.06  git: last_make_outside_of_git: false
% 2.16/1.06  
% 2.16/1.06  ------ 
% 2.16/1.06  
% 2.16/1.06  ------ Input Options
% 2.16/1.06  
% 2.16/1.06  --out_options                           all
% 2.16/1.06  --tptp_safe_out                         true
% 2.16/1.06  --problem_path                          ""
% 2.16/1.06  --include_path                          ""
% 2.16/1.06  --clausifier                            res/vclausify_rel
% 2.16/1.06  --clausifier_options                    --mode clausify
% 2.16/1.06  --stdin                                 false
% 2.16/1.06  --stats_out                             all
% 2.16/1.06  
% 2.16/1.06  ------ General Options
% 2.16/1.06  
% 2.16/1.06  --fof                                   false
% 2.16/1.06  --time_out_real                         305.
% 2.16/1.06  --time_out_virtual                      -1.
% 2.16/1.06  --symbol_type_check                     false
% 2.16/1.06  --clausify_out                          false
% 2.16/1.06  --sig_cnt_out                           false
% 2.16/1.06  --trig_cnt_out                          false
% 2.16/1.06  --trig_cnt_out_tolerance                1.
% 2.16/1.06  --trig_cnt_out_sk_spl                   false
% 2.16/1.06  --abstr_cl_out                          false
% 2.16/1.06  
% 2.16/1.06  ------ Global Options
% 2.16/1.06  
% 2.16/1.06  --schedule                              default
% 2.16/1.06  --add_important_lit                     false
% 2.16/1.06  --prop_solver_per_cl                    1000
% 2.16/1.06  --min_unsat_core                        false
% 2.16/1.06  --soft_assumptions                      false
% 2.16/1.06  --soft_lemma_size                       3
% 2.16/1.06  --prop_impl_unit_size                   0
% 2.16/1.06  --prop_impl_unit                        []
% 2.16/1.06  --share_sel_clauses                     true
% 2.16/1.06  --reset_solvers                         false
% 2.16/1.06  --bc_imp_inh                            [conj_cone]
% 2.16/1.06  --conj_cone_tolerance                   3.
% 2.16/1.06  --extra_neg_conj                        none
% 2.16/1.06  --large_theory_mode                     true
% 2.16/1.06  --prolific_symb_bound                   200
% 2.16/1.06  --lt_threshold                          2000
% 2.16/1.06  --clause_weak_htbl                      true
% 2.16/1.06  --gc_record_bc_elim                     false
% 2.16/1.06  
% 2.16/1.06  ------ Preprocessing Options
% 2.16/1.06  
% 2.16/1.06  --preprocessing_flag                    true
% 2.16/1.06  --time_out_prep_mult                    0.1
% 2.16/1.06  --splitting_mode                        input
% 2.16/1.06  --splitting_grd                         true
% 2.16/1.06  --splitting_cvd                         false
% 2.16/1.06  --splitting_cvd_svl                     false
% 2.16/1.06  --splitting_nvd                         32
% 2.16/1.06  --sub_typing                            true
% 2.16/1.06  --prep_gs_sim                           true
% 2.16/1.06  --prep_unflatten                        true
% 2.16/1.06  --prep_res_sim                          true
% 2.16/1.06  --prep_upred                            true
% 2.16/1.06  --prep_sem_filter                       exhaustive
% 2.16/1.06  --prep_sem_filter_out                   false
% 2.16/1.06  --pred_elim                             true
% 2.16/1.06  --res_sim_input                         true
% 2.16/1.06  --eq_ax_congr_red                       true
% 2.16/1.06  --pure_diseq_elim                       true
% 2.16/1.06  --brand_transform                       false
% 2.16/1.06  --non_eq_to_eq                          false
% 2.16/1.06  --prep_def_merge                        true
% 2.16/1.06  --prep_def_merge_prop_impl              false
% 2.16/1.06  --prep_def_merge_mbd                    true
% 2.16/1.06  --prep_def_merge_tr_red                 false
% 2.16/1.06  --prep_def_merge_tr_cl                  false
% 2.16/1.06  --smt_preprocessing                     true
% 2.16/1.06  --smt_ac_axioms                         fast
% 2.16/1.06  --preprocessed_out                      false
% 2.16/1.06  --preprocessed_stats                    false
% 2.16/1.06  
% 2.16/1.06  ------ Abstraction refinement Options
% 2.16/1.06  
% 2.16/1.06  --abstr_ref                             []
% 2.16/1.06  --abstr_ref_prep                        false
% 2.16/1.06  --abstr_ref_until_sat                   false
% 2.16/1.06  --abstr_ref_sig_restrict                funpre
% 2.16/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.06  --abstr_ref_under                       []
% 2.16/1.06  
% 2.16/1.06  ------ SAT Options
% 2.16/1.06  
% 2.16/1.06  --sat_mode                              false
% 2.16/1.06  --sat_fm_restart_options                ""
% 2.16/1.06  --sat_gr_def                            false
% 2.16/1.06  --sat_epr_types                         true
% 2.16/1.06  --sat_non_cyclic_types                  false
% 2.16/1.06  --sat_finite_models                     false
% 2.16/1.06  --sat_fm_lemmas                         false
% 2.16/1.06  --sat_fm_prep                           false
% 2.16/1.06  --sat_fm_uc_incr                        true
% 2.16/1.06  --sat_out_model                         small
% 2.16/1.06  --sat_out_clauses                       false
% 2.16/1.06  
% 2.16/1.06  ------ QBF Options
% 2.16/1.06  
% 2.16/1.06  --qbf_mode                              false
% 2.16/1.06  --qbf_elim_univ                         false
% 2.16/1.06  --qbf_dom_inst                          none
% 2.16/1.06  --qbf_dom_pre_inst                      false
% 2.16/1.06  --qbf_sk_in                             false
% 2.16/1.06  --qbf_pred_elim                         true
% 2.16/1.06  --qbf_split                             512
% 2.16/1.06  
% 2.16/1.06  ------ BMC1 Options
% 2.16/1.06  
% 2.16/1.06  --bmc1_incremental                      false
% 2.16/1.06  --bmc1_axioms                           reachable_all
% 2.16/1.06  --bmc1_min_bound                        0
% 2.16/1.06  --bmc1_max_bound                        -1
% 2.16/1.06  --bmc1_max_bound_default                -1
% 2.16/1.06  --bmc1_symbol_reachability              true
% 2.16/1.06  --bmc1_property_lemmas                  false
% 2.16/1.06  --bmc1_k_induction                      false
% 2.16/1.06  --bmc1_non_equiv_states                 false
% 2.16/1.06  --bmc1_deadlock                         false
% 2.16/1.06  --bmc1_ucm                              false
% 2.16/1.06  --bmc1_add_unsat_core                   none
% 2.16/1.06  --bmc1_unsat_core_children              false
% 2.16/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.06  --bmc1_out_stat                         full
% 2.16/1.06  --bmc1_ground_init                      false
% 2.16/1.06  --bmc1_pre_inst_next_state              false
% 2.16/1.06  --bmc1_pre_inst_state                   false
% 2.16/1.06  --bmc1_pre_inst_reach_state             false
% 2.16/1.06  --bmc1_out_unsat_core                   false
% 2.16/1.06  --bmc1_aig_witness_out                  false
% 2.16/1.06  --bmc1_verbose                          false
% 2.16/1.06  --bmc1_dump_clauses_tptp                false
% 2.16/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.06  --bmc1_dump_file                        -
% 2.16/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.06  --bmc1_ucm_extend_mode                  1
% 2.16/1.06  --bmc1_ucm_init_mode                    2
% 2.16/1.06  --bmc1_ucm_cone_mode                    none
% 2.16/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.06  --bmc1_ucm_relax_model                  4
% 2.16/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.06  --bmc1_ucm_layered_model                none
% 2.16/1.06  --bmc1_ucm_max_lemma_size               10
% 2.16/1.06  
% 2.16/1.06  ------ AIG Options
% 2.16/1.06  
% 2.16/1.06  --aig_mode                              false
% 2.16/1.06  
% 2.16/1.06  ------ Instantiation Options
% 2.16/1.06  
% 2.16/1.06  --instantiation_flag                    true
% 2.16/1.06  --inst_sos_flag                         false
% 2.16/1.06  --inst_sos_phase                        true
% 2.16/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.06  --inst_lit_sel_side                     num_symb
% 2.16/1.06  --inst_solver_per_active                1400
% 2.16/1.06  --inst_solver_calls_frac                1.
% 2.16/1.06  --inst_passive_queue_type               priority_queues
% 2.16/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.06  --inst_passive_queues_freq              [25;2]
% 2.16/1.06  --inst_dismatching                      true
% 2.16/1.06  --inst_eager_unprocessed_to_passive     true
% 2.16/1.06  --inst_prop_sim_given                   true
% 2.16/1.06  --inst_prop_sim_new                     false
% 2.16/1.06  --inst_subs_new                         false
% 2.16/1.06  --inst_eq_res_simp                      false
% 2.16/1.06  --inst_subs_given                       false
% 2.16/1.06  --inst_orphan_elimination               true
% 2.16/1.06  --inst_learning_loop_flag               true
% 2.16/1.06  --inst_learning_start                   3000
% 2.16/1.06  --inst_learning_factor                  2
% 2.16/1.06  --inst_start_prop_sim_after_learn       3
% 2.16/1.06  --inst_sel_renew                        solver
% 2.16/1.06  --inst_lit_activity_flag                true
% 2.16/1.06  --inst_restr_to_given                   false
% 2.16/1.06  --inst_activity_threshold               500
% 2.16/1.06  --inst_out_proof                        true
% 2.16/1.06  
% 2.16/1.06  ------ Resolution Options
% 2.16/1.06  
% 2.16/1.06  --resolution_flag                       true
% 2.16/1.06  --res_lit_sel                           adaptive
% 2.16/1.06  --res_lit_sel_side                      none
% 2.16/1.06  --res_ordering                          kbo
% 2.16/1.06  --res_to_prop_solver                    active
% 2.16/1.06  --res_prop_simpl_new                    false
% 2.16/1.06  --res_prop_simpl_given                  true
% 2.16/1.06  --res_passive_queue_type                priority_queues
% 2.16/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.06  --res_passive_queues_freq               [15;5]
% 2.16/1.06  --res_forward_subs                      full
% 2.16/1.06  --res_backward_subs                     full
% 2.16/1.06  --res_forward_subs_resolution           true
% 2.16/1.06  --res_backward_subs_resolution          true
% 2.16/1.06  --res_orphan_elimination                true
% 2.16/1.06  --res_time_limit                        2.
% 2.16/1.06  --res_out_proof                         true
% 2.16/1.06  
% 2.16/1.06  ------ Superposition Options
% 2.16/1.06  
% 2.16/1.06  --superposition_flag                    true
% 2.16/1.06  --sup_passive_queue_type                priority_queues
% 2.16/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.06  --demod_completeness_check              fast
% 2.16/1.06  --demod_use_ground                      true
% 2.16/1.06  --sup_to_prop_solver                    passive
% 2.16/1.06  --sup_prop_simpl_new                    true
% 2.16/1.06  --sup_prop_simpl_given                  true
% 2.16/1.06  --sup_fun_splitting                     false
% 2.16/1.06  --sup_smt_interval                      50000
% 2.16/1.06  
% 2.16/1.06  ------ Superposition Simplification Setup
% 2.16/1.06  
% 2.16/1.06  --sup_indices_passive                   []
% 2.16/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_full_bw                           [BwDemod]
% 2.16/1.06  --sup_immed_triv                        [TrivRules]
% 2.16/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_immed_bw_main                     []
% 2.16/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.06  
% 2.16/1.06  ------ Combination Options
% 2.16/1.06  
% 2.16/1.06  --comb_res_mult                         3
% 2.16/1.06  --comb_sup_mult                         2
% 2.16/1.06  --comb_inst_mult                        10
% 2.16/1.06  
% 2.16/1.06  ------ Debug Options
% 2.16/1.06  
% 2.16/1.06  --dbg_backtrace                         false
% 2.16/1.06  --dbg_dump_prop_clauses                 false
% 2.16/1.06  --dbg_dump_prop_clauses_file            -
% 2.16/1.06  --dbg_out_stat                          false
% 2.16/1.06  ------ Parsing...
% 2.16/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.06  
% 2.16/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.16/1.06  
% 2.16/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.06  
% 2.16/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.06  ------ Proving...
% 2.16/1.06  ------ Problem Properties 
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  clauses                                 17
% 2.16/1.06  conjectures                             6
% 2.16/1.06  EPR                                     3
% 2.16/1.06  Horn                                    12
% 2.16/1.06  unary                                   6
% 2.16/1.06  binary                                  5
% 2.16/1.06  lits                                    41
% 2.16/1.06  lits eq                                 12
% 2.16/1.06  fd_pure                                 0
% 2.16/1.06  fd_pseudo                               0
% 2.16/1.06  fd_cond                                 3
% 2.16/1.06  fd_pseudo_cond                          0
% 2.16/1.06  AC symbols                              0
% 2.16/1.06  
% 2.16/1.06  ------ Schedule dynamic 5 is on 
% 2.16/1.06  
% 2.16/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  ------ 
% 2.16/1.06  Current options:
% 2.16/1.06  ------ 
% 2.16/1.06  
% 2.16/1.06  ------ Input Options
% 2.16/1.06  
% 2.16/1.06  --out_options                           all
% 2.16/1.06  --tptp_safe_out                         true
% 2.16/1.06  --problem_path                          ""
% 2.16/1.06  --include_path                          ""
% 2.16/1.06  --clausifier                            res/vclausify_rel
% 2.16/1.06  --clausifier_options                    --mode clausify
% 2.16/1.06  --stdin                                 false
% 2.16/1.06  --stats_out                             all
% 2.16/1.06  
% 2.16/1.06  ------ General Options
% 2.16/1.06  
% 2.16/1.06  --fof                                   false
% 2.16/1.06  --time_out_real                         305.
% 2.16/1.06  --time_out_virtual                      -1.
% 2.16/1.06  --symbol_type_check                     false
% 2.16/1.06  --clausify_out                          false
% 2.16/1.06  --sig_cnt_out                           false
% 2.16/1.06  --trig_cnt_out                          false
% 2.16/1.06  --trig_cnt_out_tolerance                1.
% 2.16/1.06  --trig_cnt_out_sk_spl                   false
% 2.16/1.06  --abstr_cl_out                          false
% 2.16/1.06  
% 2.16/1.06  ------ Global Options
% 2.16/1.06  
% 2.16/1.06  --schedule                              default
% 2.16/1.06  --add_important_lit                     false
% 2.16/1.06  --prop_solver_per_cl                    1000
% 2.16/1.06  --min_unsat_core                        false
% 2.16/1.06  --soft_assumptions                      false
% 2.16/1.06  --soft_lemma_size                       3
% 2.16/1.06  --prop_impl_unit_size                   0
% 2.16/1.06  --prop_impl_unit                        []
% 2.16/1.06  --share_sel_clauses                     true
% 2.16/1.06  --reset_solvers                         false
% 2.16/1.06  --bc_imp_inh                            [conj_cone]
% 2.16/1.06  --conj_cone_tolerance                   3.
% 2.16/1.06  --extra_neg_conj                        none
% 2.16/1.06  --large_theory_mode                     true
% 2.16/1.06  --prolific_symb_bound                   200
% 2.16/1.06  --lt_threshold                          2000
% 2.16/1.06  --clause_weak_htbl                      true
% 2.16/1.06  --gc_record_bc_elim                     false
% 2.16/1.06  
% 2.16/1.06  ------ Preprocessing Options
% 2.16/1.06  
% 2.16/1.06  --preprocessing_flag                    true
% 2.16/1.06  --time_out_prep_mult                    0.1
% 2.16/1.06  --splitting_mode                        input
% 2.16/1.06  --splitting_grd                         true
% 2.16/1.06  --splitting_cvd                         false
% 2.16/1.06  --splitting_cvd_svl                     false
% 2.16/1.06  --splitting_nvd                         32
% 2.16/1.06  --sub_typing                            true
% 2.16/1.06  --prep_gs_sim                           true
% 2.16/1.06  --prep_unflatten                        true
% 2.16/1.06  --prep_res_sim                          true
% 2.16/1.06  --prep_upred                            true
% 2.16/1.06  --prep_sem_filter                       exhaustive
% 2.16/1.06  --prep_sem_filter_out                   false
% 2.16/1.06  --pred_elim                             true
% 2.16/1.06  --res_sim_input                         true
% 2.16/1.06  --eq_ax_congr_red                       true
% 2.16/1.06  --pure_diseq_elim                       true
% 2.16/1.06  --brand_transform                       false
% 2.16/1.06  --non_eq_to_eq                          false
% 2.16/1.06  --prep_def_merge                        true
% 2.16/1.06  --prep_def_merge_prop_impl              false
% 2.16/1.06  --prep_def_merge_mbd                    true
% 2.16/1.06  --prep_def_merge_tr_red                 false
% 2.16/1.06  --prep_def_merge_tr_cl                  false
% 2.16/1.06  --smt_preprocessing                     true
% 2.16/1.06  --smt_ac_axioms                         fast
% 2.16/1.06  --preprocessed_out                      false
% 2.16/1.06  --preprocessed_stats                    false
% 2.16/1.06  
% 2.16/1.06  ------ Abstraction refinement Options
% 2.16/1.06  
% 2.16/1.06  --abstr_ref                             []
% 2.16/1.06  --abstr_ref_prep                        false
% 2.16/1.06  --abstr_ref_until_sat                   false
% 2.16/1.06  --abstr_ref_sig_restrict                funpre
% 2.16/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.06  --abstr_ref_under                       []
% 2.16/1.06  
% 2.16/1.06  ------ SAT Options
% 2.16/1.06  
% 2.16/1.06  --sat_mode                              false
% 2.16/1.06  --sat_fm_restart_options                ""
% 2.16/1.06  --sat_gr_def                            false
% 2.16/1.06  --sat_epr_types                         true
% 2.16/1.06  --sat_non_cyclic_types                  false
% 2.16/1.06  --sat_finite_models                     false
% 2.16/1.06  --sat_fm_lemmas                         false
% 2.16/1.06  --sat_fm_prep                           false
% 2.16/1.06  --sat_fm_uc_incr                        true
% 2.16/1.06  --sat_out_model                         small
% 2.16/1.06  --sat_out_clauses                       false
% 2.16/1.06  
% 2.16/1.06  ------ QBF Options
% 2.16/1.06  
% 2.16/1.06  --qbf_mode                              false
% 2.16/1.06  --qbf_elim_univ                         false
% 2.16/1.06  --qbf_dom_inst                          none
% 2.16/1.06  --qbf_dom_pre_inst                      false
% 2.16/1.06  --qbf_sk_in                             false
% 2.16/1.06  --qbf_pred_elim                         true
% 2.16/1.06  --qbf_split                             512
% 2.16/1.06  
% 2.16/1.06  ------ BMC1 Options
% 2.16/1.06  
% 2.16/1.06  --bmc1_incremental                      false
% 2.16/1.06  --bmc1_axioms                           reachable_all
% 2.16/1.06  --bmc1_min_bound                        0
% 2.16/1.06  --bmc1_max_bound                        -1
% 2.16/1.06  --bmc1_max_bound_default                -1
% 2.16/1.06  --bmc1_symbol_reachability              true
% 2.16/1.06  --bmc1_property_lemmas                  false
% 2.16/1.06  --bmc1_k_induction                      false
% 2.16/1.06  --bmc1_non_equiv_states                 false
% 2.16/1.06  --bmc1_deadlock                         false
% 2.16/1.06  --bmc1_ucm                              false
% 2.16/1.06  --bmc1_add_unsat_core                   none
% 2.16/1.06  --bmc1_unsat_core_children              false
% 2.16/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.06  --bmc1_out_stat                         full
% 2.16/1.06  --bmc1_ground_init                      false
% 2.16/1.06  --bmc1_pre_inst_next_state              false
% 2.16/1.06  --bmc1_pre_inst_state                   false
% 2.16/1.06  --bmc1_pre_inst_reach_state             false
% 2.16/1.06  --bmc1_out_unsat_core                   false
% 2.16/1.06  --bmc1_aig_witness_out                  false
% 2.16/1.06  --bmc1_verbose                          false
% 2.16/1.06  --bmc1_dump_clauses_tptp                false
% 2.16/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.06  --bmc1_dump_file                        -
% 2.16/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.06  --bmc1_ucm_extend_mode                  1
% 2.16/1.06  --bmc1_ucm_init_mode                    2
% 2.16/1.06  --bmc1_ucm_cone_mode                    none
% 2.16/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.06  --bmc1_ucm_relax_model                  4
% 2.16/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.06  --bmc1_ucm_layered_model                none
% 2.16/1.06  --bmc1_ucm_max_lemma_size               10
% 2.16/1.06  
% 2.16/1.06  ------ AIG Options
% 2.16/1.06  
% 2.16/1.06  --aig_mode                              false
% 2.16/1.06  
% 2.16/1.06  ------ Instantiation Options
% 2.16/1.06  
% 2.16/1.06  --instantiation_flag                    true
% 2.16/1.06  --inst_sos_flag                         false
% 2.16/1.06  --inst_sos_phase                        true
% 2.16/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.06  --inst_lit_sel_side                     none
% 2.16/1.06  --inst_solver_per_active                1400
% 2.16/1.06  --inst_solver_calls_frac                1.
% 2.16/1.06  --inst_passive_queue_type               priority_queues
% 2.16/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.06  --inst_passive_queues_freq              [25;2]
% 2.16/1.06  --inst_dismatching                      true
% 2.16/1.06  --inst_eager_unprocessed_to_passive     true
% 2.16/1.06  --inst_prop_sim_given                   true
% 2.16/1.06  --inst_prop_sim_new                     false
% 2.16/1.06  --inst_subs_new                         false
% 2.16/1.06  --inst_eq_res_simp                      false
% 2.16/1.06  --inst_subs_given                       false
% 2.16/1.06  --inst_orphan_elimination               true
% 2.16/1.06  --inst_learning_loop_flag               true
% 2.16/1.06  --inst_learning_start                   3000
% 2.16/1.06  --inst_learning_factor                  2
% 2.16/1.06  --inst_start_prop_sim_after_learn       3
% 2.16/1.06  --inst_sel_renew                        solver
% 2.16/1.06  --inst_lit_activity_flag                true
% 2.16/1.06  --inst_restr_to_given                   false
% 2.16/1.06  --inst_activity_threshold               500
% 2.16/1.06  --inst_out_proof                        true
% 2.16/1.06  
% 2.16/1.06  ------ Resolution Options
% 2.16/1.06  
% 2.16/1.06  --resolution_flag                       false
% 2.16/1.06  --res_lit_sel                           adaptive
% 2.16/1.06  --res_lit_sel_side                      none
% 2.16/1.06  --res_ordering                          kbo
% 2.16/1.06  --res_to_prop_solver                    active
% 2.16/1.06  --res_prop_simpl_new                    false
% 2.16/1.06  --res_prop_simpl_given                  true
% 2.16/1.06  --res_passive_queue_type                priority_queues
% 2.16/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.06  --res_passive_queues_freq               [15;5]
% 2.16/1.06  --res_forward_subs                      full
% 2.16/1.06  --res_backward_subs                     full
% 2.16/1.06  --res_forward_subs_resolution           true
% 2.16/1.06  --res_backward_subs_resolution          true
% 2.16/1.06  --res_orphan_elimination                true
% 2.16/1.06  --res_time_limit                        2.
% 2.16/1.06  --res_out_proof                         true
% 2.16/1.06  
% 2.16/1.06  ------ Superposition Options
% 2.16/1.06  
% 2.16/1.06  --superposition_flag                    true
% 2.16/1.06  --sup_passive_queue_type                priority_queues
% 2.16/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.06  --demod_completeness_check              fast
% 2.16/1.06  --demod_use_ground                      true
% 2.16/1.06  --sup_to_prop_solver                    passive
% 2.16/1.06  --sup_prop_simpl_new                    true
% 2.16/1.06  --sup_prop_simpl_given                  true
% 2.16/1.06  --sup_fun_splitting                     false
% 2.16/1.06  --sup_smt_interval                      50000
% 2.16/1.06  
% 2.16/1.06  ------ Superposition Simplification Setup
% 2.16/1.06  
% 2.16/1.06  --sup_indices_passive                   []
% 2.16/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_full_bw                           [BwDemod]
% 2.16/1.06  --sup_immed_triv                        [TrivRules]
% 2.16/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_immed_bw_main                     []
% 2.16/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.06  
% 2.16/1.06  ------ Combination Options
% 2.16/1.06  
% 2.16/1.06  --comb_res_mult                         3
% 2.16/1.06  --comb_sup_mult                         2
% 2.16/1.06  --comb_inst_mult                        10
% 2.16/1.06  
% 2.16/1.06  ------ Debug Options
% 2.16/1.06  
% 2.16/1.06  --dbg_backtrace                         false
% 2.16/1.06  --dbg_dump_prop_clauses                 false
% 2.16/1.06  --dbg_dump_prop_clauses_file            -
% 2.16/1.06  --dbg_out_stat                          false
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  ------ Proving...
% 2.16/1.06  
% 2.16/1.06  
% 2.16/1.06  % SZS status Theorem for theBenchmark.p
% 2.16/1.06  
% 2.16/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.06  
% 2.16/1.06  fof(f8,conjecture,(
% 2.16/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.06  
% 2.16/1.06  fof(f9,negated_conjecture,(
% 2.16/1.06    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.16/1.06    inference(negated_conjecture,[],[f8])).
% 2.16/1.06  
% 2.16/1.06  fof(f18,plain,(
% 2.16/1.06    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.16/1.06    inference(ennf_transformation,[],[f9])).
% 2.16/1.06  
% 2.16/1.06  fof(f19,plain,(
% 2.16/1.06    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.16/1.06    inference(flattening,[],[f18])).
% 2.16/1.06  
% 2.16/1.06  fof(f25,plain,(
% 2.16/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.16/1.06    introduced(choice_axiom,[])).
% 2.16/1.06  
% 2.16/1.06  fof(f24,plain,(
% 2.16/1.06    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.16/1.06    introduced(choice_axiom,[])).
% 2.16/1.06  
% 2.16/1.06  fof(f23,plain,(
% 2.16/1.06    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.16/1.06    introduced(choice_axiom,[])).
% 2.16/1.06  
% 2.16/1.06  fof(f22,plain,(
% 2.16/1.06    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.16/1.06    introduced(choice_axiom,[])).
% 2.16/1.06  
% 2.16/1.06  fof(f26,plain,(
% 2.16/1.06    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f25,f24,f23,f22])).
% 2.16/1.06  
% 2.16/1.06  fof(f42,plain,(
% 2.16/1.06    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.16/1.06    inference(cnf_transformation,[],[f26])).
% 2.16/1.06  
% 2.16/1.06  fof(f5,axiom,(
% 2.16/1.06    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.06  
% 2.16/1.06  fof(f33,plain,(
% 2.16/1.06    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.16/1.06    inference(cnf_transformation,[],[f5])).
% 2.16/1.06  
% 2.16/1.06  fof(f49,plain,(
% 2.16/1.06    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.16/1.07    inference(definition_unfolding,[],[f42,f33])).
% 2.16/1.07  
% 2.16/1.07  fof(f7,axiom,(
% 2.16/1.07    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f17,plain,(
% 2.16/1.07    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.16/1.07    inference(ennf_transformation,[],[f7])).
% 2.16/1.07  
% 2.16/1.07  fof(f38,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(cnf_transformation,[],[f17])).
% 2.16/1.07  
% 2.16/1.07  fof(f45,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(definition_unfolding,[],[f38,f33])).
% 2.16/1.07  
% 2.16/1.07  fof(f37,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(cnf_transformation,[],[f17])).
% 2.16/1.07  
% 2.16/1.07  fof(f46,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(definition_unfolding,[],[f37,f33])).
% 2.16/1.07  
% 2.16/1.07  fof(f43,plain,(
% 2.16/1.07    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.16/1.07    inference(cnf_transformation,[],[f26])).
% 2.16/1.07  
% 2.16/1.07  fof(f48,plain,(
% 2.16/1.07    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.16/1.07    inference(definition_unfolding,[],[f43,f33])).
% 2.16/1.07  
% 2.16/1.07  fof(f3,axiom,(
% 2.16/1.07    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f31,plain,(
% 2.16/1.07    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.16/1.07    inference(cnf_transformation,[],[f3])).
% 2.16/1.07  
% 2.16/1.07  fof(f4,axiom,(
% 2.16/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f11,plain,(
% 2.16/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.16/1.07    inference(unused_predicate_definition_removal,[],[f4])).
% 2.16/1.07  
% 2.16/1.07  fof(f15,plain,(
% 2.16/1.07    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.16/1.07    inference(ennf_transformation,[],[f11])).
% 2.16/1.07  
% 2.16/1.07  fof(f32,plain,(
% 2.16/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.16/1.07    inference(cnf_transformation,[],[f15])).
% 2.16/1.07  
% 2.16/1.07  fof(f41,plain,(
% 2.16/1.07    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.16/1.07    inference(cnf_transformation,[],[f26])).
% 2.16/1.07  
% 2.16/1.07  fof(f6,axiom,(
% 2.16/1.07    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f16,plain,(
% 2.16/1.07    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.16/1.07    inference(ennf_transformation,[],[f6])).
% 2.16/1.07  
% 2.16/1.07  fof(f35,plain,(
% 2.16/1.07    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.16/1.07    inference(cnf_transformation,[],[f16])).
% 2.16/1.07  
% 2.16/1.07  fof(f1,axiom,(
% 2.16/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f10,plain,(
% 2.16/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.16/1.07    inference(rectify,[],[f1])).
% 2.16/1.07  
% 2.16/1.07  fof(f12,plain,(
% 2.16/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.16/1.07    inference(ennf_transformation,[],[f10])).
% 2.16/1.07  
% 2.16/1.07  fof(f20,plain,(
% 2.16/1.07    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.16/1.07    introduced(choice_axiom,[])).
% 2.16/1.07  
% 2.16/1.07  fof(f21,plain,(
% 2.16/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.16/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).
% 2.16/1.07  
% 2.16/1.07  fof(f29,plain,(
% 2.16/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.16/1.07    inference(cnf_transformation,[],[f21])).
% 2.16/1.07  
% 2.16/1.07  fof(f2,axiom,(
% 2.16/1.07    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.16/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.07  
% 2.16/1.07  fof(f13,plain,(
% 2.16/1.07    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.16/1.07    inference(ennf_transformation,[],[f2])).
% 2.16/1.07  
% 2.16/1.07  fof(f14,plain,(
% 2.16/1.07    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.16/1.07    inference(flattening,[],[f13])).
% 2.16/1.07  
% 2.16/1.07  fof(f30,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.16/1.07    inference(cnf_transformation,[],[f14])).
% 2.16/1.07  
% 2.16/1.07  fof(f36,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(cnf_transformation,[],[f17])).
% 2.16/1.07  
% 2.16/1.07  fof(f47,plain,(
% 2.16/1.07    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.16/1.07    inference(definition_unfolding,[],[f36,f33])).
% 2.16/1.07  
% 2.16/1.07  fof(f44,plain,(
% 2.16/1.07    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.16/1.07    inference(cnf_transformation,[],[f26])).
% 2.16/1.07  
% 2.16/1.07  fof(f34,plain,(
% 2.16/1.07    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.16/1.07    inference(cnf_transformation,[],[f16])).
% 2.16/1.07  
% 2.16/1.07  fof(f40,plain,(
% 2.16/1.07    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.16/1.07    inference(cnf_transformation,[],[f26])).
% 2.16/1.07  
% 2.16/1.07  fof(f39,plain,(
% 2.16/1.07    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.16/1.07    inference(cnf_transformation,[],[f26])).
% 2.16/1.07  
% 2.16/1.07  cnf(c_13,negated_conjecture,
% 2.16/1.07      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.16/1.07      inference(cnf_transformation,[],[f49]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_834,plain,
% 2.16/1.07      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_8,plain,
% 2.16/1.07      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.16/1.07      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.16/1.07      | k1_xboole_0 = X3
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | k1_xboole_0 = X1 ),
% 2.16/1.07      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_839,plain,
% 2.16/1.07      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.16/1.07      | k1_xboole_0 = X1
% 2.16/1.07      | k1_xboole_0 = X0
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3055,plain,
% 2.16/1.07      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.16/1.07      | sK3 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_834,c_839]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_9,plain,
% 2.16/1.07      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.16/1.07      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.16/1.07      | k1_xboole_0 = X3
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | k1_xboole_0 = X1 ),
% 2.16/1.07      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_838,plain,
% 2.16/1.07      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.16/1.07      | k1_xboole_0 = X1
% 2.16/1.07      | k1_xboole_0 = X0
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3138,plain,
% 2.16/1.07      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.16/1.07      | sK3 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_834,c_838]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_12,negated_conjecture,
% 2.16/1.07      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.16/1.07      inference(cnf_transformation,[],[f48]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_4,plain,
% 2.16/1.07      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.16/1.07      inference(cnf_transformation,[],[f31]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_42,plain,
% 2.16/1.07      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_4]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_5,plain,
% 2.16/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.16/1.07      inference(cnf_transformation,[],[f32]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_14,negated_conjecture,
% 2.16/1.07      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.16/1.07      inference(cnf_transformation,[],[f41]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_199,plain,
% 2.16/1.07      ( r1_tarski(X0,X1)
% 2.16/1.07      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK3)
% 2.16/1.07      | sK6 != X0 ),
% 2.16/1.07      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_200,plain,
% 2.16/1.07      ( r1_tarski(sK6,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 2.16/1.07      inference(unflattening,[status(thm)],[c_199]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_202,plain,
% 2.16/1.07      ( r1_tarski(sK6,k1_xboole_0)
% 2.16/1.07      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_200]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_520,plain,( X0 = X0 ),theory(equality) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_543,plain,
% 2.16/1.07      ( k1_xboole_0 = k1_xboole_0 ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_520]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_6,plain,
% 2.16/1.07      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.16/1.07      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.16/1.07      inference(cnf_transformation,[],[f35]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_980,plain,
% 2.16/1.07      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.16/1.07      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_6]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_524,plain,
% 2.16/1.07      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.16/1.07      theory(equality) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1298,plain,
% 2.16/1.07      ( X0 != sK3 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_524]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1303,plain,
% 2.16/1.07      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
% 2.16/1.07      | k1_xboole_0 != sK3 ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_1298]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_0,plain,
% 2.16/1.07      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.16/1.07      inference(cnf_transformation,[],[f29]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1027,plain,
% 2.16/1.07      ( ~ r2_hidden(k2_mcart_1(sK7),X0)
% 2.16/1.07      | ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.16/1.07      | ~ r1_xboole_0(X0,sK6) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_0]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2199,plain,
% 2.16/1.07      ( ~ r2_hidden(k2_mcart_1(sK7),sK6) | ~ r1_xboole_0(sK6,sK6) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_1027]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_521,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2270,plain,
% 2.16/1.07      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_521]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2271,plain,
% 2.16/1.07      ( sK3 != k1_xboole_0
% 2.16/1.07      | k1_xboole_0 = sK3
% 2.16/1.07      | k1_xboole_0 != k1_xboole_0 ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_2270]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3,plain,
% 2.16/1.07      ( ~ r1_tarski(X0,X1)
% 2.16/1.07      | ~ r1_tarski(X2,X3)
% 2.16/1.07      | ~ r1_xboole_0(X3,X1)
% 2.16/1.07      | r1_xboole_0(X2,X0) ),
% 2.16/1.07      inference(cnf_transformation,[],[f30]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1232,plain,
% 2.16/1.07      ( ~ r1_tarski(X0,X1)
% 2.16/1.07      | ~ r1_tarski(sK6,X2)
% 2.16/1.07      | ~ r1_xboole_0(X1,X2)
% 2.16/1.07      | r1_xboole_0(X0,sK6) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_3]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3325,plain,
% 2.16/1.07      ( ~ r1_tarski(sK6,X0)
% 2.16/1.07      | ~ r1_tarski(sK6,X1)
% 2.16/1.07      | ~ r1_xboole_0(X0,X1)
% 2.16/1.07      | r1_xboole_0(sK6,sK6) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_1232]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3327,plain,
% 2.16/1.07      ( ~ r1_tarski(sK6,k1_xboole_0)
% 2.16/1.07      | r1_xboole_0(sK6,sK6)
% 2.16/1.07      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_3325]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3434,plain,
% 2.16/1.07      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_3138,c_12,c_42,c_202,c_543,c_980,c_1303,c_2199,c_2271,
% 2.16/1.07                 c_3327]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10,plain,
% 2.16/1.07      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.16/1.07      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.16/1.07      | k1_xboole_0 = X3
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | k1_xboole_0 = X1 ),
% 2.16/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_837,plain,
% 2.16/1.07      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.16/1.07      | k1_xboole_0 = X1
% 2.16/1.07      | k1_xboole_0 = X0
% 2.16/1.07      | k1_xboole_0 = X2
% 2.16/1.07      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3131,plain,
% 2.16/1.07      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.16/1.07      | sK3 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_834,c_837]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_11,negated_conjecture,
% 2.16/1.07      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.16/1.07      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.16/1.07      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.16/1.07      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_836,plain,
% 2.16/1.07      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.16/1.07      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3260,plain,
% 2.16/1.07      ( sK3 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.16/1.07      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_3131,c_836]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_21,plain,
% 2.16/1.07      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_7,plain,
% 2.16/1.07      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.16/1.07      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.16/1.07      inference(cnf_transformation,[],[f34]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_983,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.16/1.07      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_984,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.16/1.07      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1046,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.16/1.07      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1050,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.16/1.07      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3440,plain,
% 2.16/1.07      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.16/1.07      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0 ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_3260,c_12,c_21,c_42,c_202,c_543,c_980,c_984,c_1050,
% 2.16/1.07                 c_1303,c_2199,c_2271,c_3327]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3441,plain,
% 2.16/1.07      ( sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.16/1.07      inference(renaming,[status(thm)],[c_3440]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3448,plain,
% 2.16/1.07      ( sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.16/1.07      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_3434,c_3441]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1047,plain,
% 2.16/1.07      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.16/1.07      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_6]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1048,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.16/1.07      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10337,plain,
% 2.16/1.07      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0 ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_3448,c_21,c_984,c_1048]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10338,plain,
% 2.16/1.07      ( sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.16/1.07      inference(renaming,[status(thm)],[c_10337]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10344,plain,
% 2.16/1.07      ( sK3 = k1_xboole_0
% 2.16/1.07      | sK2 = k1_xboole_0
% 2.16/1.07      | sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_3055,c_10338]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_981,plain,
% 2.16/1.07      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
% 2.16/1.07      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10347,plain,
% 2.16/1.07      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_10344,c_12,c_21,c_42,c_202,c_543,c_980,c_981,c_1303,
% 2.16/1.07                 c_2199,c_2271,c_3327]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10348,plain,
% 2.16/1.07      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(renaming,[status(thm)],[c_10347]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10361,plain,
% 2.16/1.07      ( sK1 = k1_xboole_0
% 2.16/1.07      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.16/1.07      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.16/1.07      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_10348,c_836]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_41,plain,
% 2.16/1.07      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_43,plain,
% 2.16/1.07      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_41]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_15,negated_conjecture,
% 2.16/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.16/1.07      inference(cnf_transformation,[],[f40]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_832,plain,
% 2.16/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_842,plain,
% 2.16/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.16/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1139,plain,
% 2.16/1.07      ( r1_tarski(sK5,sK2) = iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_832,c_842]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_844,plain,
% 2.16/1.07      ( r1_tarski(X0,X1) != iProver_top
% 2.16/1.07      | r1_tarski(X2,X3) != iProver_top
% 2.16/1.07      | r1_xboole_0(X3,X1) != iProver_top
% 2.16/1.07      | r1_xboole_0(X2,X0) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3020,plain,
% 2.16/1.07      ( r1_tarski(X0,X1) != iProver_top
% 2.16/1.07      | r1_xboole_0(X0,sK5) = iProver_top
% 2.16/1.07      | r1_xboole_0(X1,sK2) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_1139,c_844]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_6160,plain,
% 2.16/1.07      ( r1_xboole_0(sK5,sK5) = iProver_top
% 2.16/1.07      | r1_xboole_0(sK2,sK2) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_1139,c_3020]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1201,plain,
% 2.16/1.07      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0)
% 2.16/1.07      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
% 2.16/1.07      | ~ r1_xboole_0(X0,sK5) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_0]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2919,plain,
% 2.16/1.07      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
% 2.16/1.07      | ~ r1_xboole_0(sK5,sK5) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_1201]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2920,plain,
% 2.16/1.07      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.16/1.07      | r1_xboole_0(sK5,sK5) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_2919]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_7461,plain,
% 2.16/1.07      ( r1_xboole_0(sK2,sK2) != iProver_top ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_6160,c_21,c_984,c_1048,c_2920]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10353,plain,
% 2.16/1.07      ( sK1 = k1_xboole_0
% 2.16/1.07      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_10348,c_7461]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10698,plain,
% 2.16/1.07      ( sK1 = k1_xboole_0 ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_10361,c_43,c_10353]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_16,negated_conjecture,
% 2.16/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.16/1.07      inference(cnf_transformation,[],[f39]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_831,plain,
% 2.16/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1140,plain,
% 2.16/1.07      ( r1_tarski(sK4,sK1) = iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_831,c_842]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_3021,plain,
% 2.16/1.07      ( r1_tarski(X0,X1) != iProver_top
% 2.16/1.07      | r1_xboole_0(X0,sK4) = iProver_top
% 2.16/1.07      | r1_xboole_0(X1,sK1) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_1140,c_844]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_8755,plain,
% 2.16/1.07      ( r1_xboole_0(sK4,sK4) = iProver_top
% 2.16/1.07      | r1_xboole_0(sK1,sK1) != iProver_top ),
% 2.16/1.07      inference(superposition,[status(thm)],[c_1140,c_3021]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_1191,plain,
% 2.16/1.07      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),X0)
% 2.16/1.07      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.16/1.07      | ~ r1_xboole_0(X0,sK4) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_0]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2916,plain,
% 2.16/1.07      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.16/1.07      | ~ r1_xboole_0(sK4,sK4) ),
% 2.16/1.07      inference(instantiation,[status(thm)],[c_1191]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_2917,plain,
% 2.16/1.07      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.16/1.07      | r1_xboole_0(sK4,sK4) != iProver_top ),
% 2.16/1.07      inference(predicate_to_equality,[status(thm)],[c_2916]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10331,plain,
% 2.16/1.07      ( r1_xboole_0(sK1,sK1) != iProver_top ),
% 2.16/1.07      inference(global_propositional_subsumption,
% 2.16/1.07                [status(thm)],
% 2.16/1.07                [c_8755,c_21,c_984,c_1050,c_2917]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(c_10701,plain,
% 2.16/1.07      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.16/1.07      inference(demodulation,[status(thm)],[c_10698,c_10331]) ).
% 2.16/1.07  
% 2.16/1.07  cnf(contradiction,plain,
% 2.16/1.07      ( $false ),
% 2.16/1.07      inference(minisat,[status(thm)],[c_10701,c_43]) ).
% 2.16/1.07  
% 2.16/1.07  
% 2.16/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.07  
% 2.16/1.07  ------                               Statistics
% 2.16/1.07  
% 2.16/1.07  ------ General
% 2.16/1.07  
% 2.16/1.07  abstr_ref_over_cycles:                  0
% 2.16/1.07  abstr_ref_under_cycles:                 0
% 2.16/1.07  gc_basic_clause_elim:                   0
% 2.16/1.07  forced_gc_time:                         0
% 2.16/1.07  parsing_time:                           0.01
% 2.16/1.07  unif_index_cands_time:                  0.
% 2.16/1.07  unif_index_add_time:                    0.
% 2.16/1.07  orderings_time:                         0.
% 2.16/1.07  out_proof_time:                         0.013
% 2.16/1.07  total_time:                             0.297
% 2.16/1.07  num_of_symbols:                         51
% 2.16/1.07  num_of_terms:                           12650
% 2.16/1.07  
% 2.16/1.07  ------ Preprocessing
% 2.16/1.07  
% 2.16/1.07  num_of_splits:                          0
% 2.16/1.07  num_of_split_atoms:                     0
% 2.16/1.07  num_of_reused_defs:                     0
% 2.16/1.07  num_eq_ax_congr_red:                    10
% 2.16/1.07  num_of_sem_filtered_clauses:            1
% 2.16/1.07  num_of_subtypes:                        0
% 2.16/1.07  monotx_restored_types:                  0
% 2.16/1.07  sat_num_of_epr_types:                   0
% 2.16/1.07  sat_num_of_non_cyclic_types:            0
% 2.16/1.07  sat_guarded_non_collapsed_types:        0
% 2.16/1.07  num_pure_diseq_elim:                    0
% 2.16/1.07  simp_replaced_by:                       0
% 2.16/1.07  res_preprocessed:                       76
% 2.16/1.07  prep_upred:                             0
% 2.16/1.07  prep_unflattend:                        16
% 2.16/1.07  smt_new_axioms:                         0
% 2.16/1.07  pred_elim_cands:                        4
% 2.16/1.07  pred_elim:                              0
% 2.16/1.07  pred_elim_cl:                           0
% 2.16/1.07  pred_elim_cycles:                       1
% 2.16/1.07  merged_defs:                            0
% 2.16/1.07  merged_defs_ncl:                        0
% 2.16/1.07  bin_hyper_res:                          0
% 2.16/1.07  prep_cycles:                            3
% 2.16/1.07  pred_elim_time:                         0.005
% 2.16/1.07  splitting_time:                         0.
% 2.16/1.07  sem_filter_time:                        0.
% 2.16/1.07  monotx_time:                            0.
% 2.16/1.07  subtype_inf_time:                       0.
% 2.16/1.07  
% 2.16/1.07  ------ Problem properties
% 2.16/1.07  
% 2.16/1.07  clauses:                                17
% 2.16/1.07  conjectures:                            6
% 2.16/1.07  epr:                                    3
% 2.16/1.07  horn:                                   12
% 2.16/1.07  ground:                                 6
% 2.16/1.07  unary:                                  6
% 2.16/1.07  binary:                                 5
% 2.16/1.07  lits:                                   41
% 2.16/1.07  lits_eq:                                12
% 2.16/1.07  fd_pure:                                0
% 2.16/1.07  fd_pseudo:                              0
% 2.16/1.07  fd_cond:                                3
% 2.16/1.07  fd_pseudo_cond:                         0
% 2.16/1.07  ac_symbols:                             0
% 2.16/1.07  
% 2.16/1.07  ------ Propositional Solver
% 2.16/1.07  
% 2.16/1.07  prop_solver_calls:                      25
% 2.16/1.07  prop_fast_solver_calls:                 624
% 2.16/1.07  smt_solver_calls:                       0
% 2.16/1.07  smt_fast_solver_calls:                  0
% 2.16/1.07  prop_num_of_clauses:                    4292
% 2.16/1.07  prop_preprocess_simplified:             10998
% 2.16/1.07  prop_fo_subsumed:                       12
% 2.16/1.07  prop_solver_time:                       0.
% 2.16/1.07  smt_solver_time:                        0.
% 2.16/1.07  smt_fast_solver_time:                   0.
% 2.16/1.07  prop_fast_solver_time:                  0.
% 2.16/1.07  prop_unsat_core_time:                   0.
% 2.16/1.07  
% 2.16/1.07  ------ QBF
% 2.16/1.07  
% 2.16/1.07  qbf_q_res:                              0
% 2.16/1.07  qbf_num_tautologies:                    0
% 2.16/1.07  qbf_prep_cycles:                        0
% 2.16/1.07  
% 2.16/1.07  ------ BMC1
% 2.16/1.07  
% 2.16/1.07  bmc1_current_bound:                     -1
% 2.16/1.07  bmc1_last_solved_bound:                 -1
% 2.16/1.07  bmc1_unsat_core_size:                   -1
% 2.16/1.07  bmc1_unsat_core_parents_size:           -1
% 2.16/1.07  bmc1_merge_next_fun:                    0
% 2.16/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.07  
% 2.16/1.07  ------ Instantiation
% 2.16/1.07  
% 2.16/1.07  inst_num_of_clauses:                    1240
% 2.16/1.07  inst_num_in_passive:                    761
% 2.16/1.07  inst_num_in_active:                     293
% 2.16/1.07  inst_num_in_unprocessed:                186
% 2.16/1.07  inst_num_of_loops:                      300
% 2.16/1.07  inst_num_of_learning_restarts:          0
% 2.16/1.07  inst_num_moves_active_passive:          6
% 2.16/1.07  inst_lit_activity:                      0
% 2.16/1.07  inst_lit_activity_moves:                0
% 2.16/1.07  inst_num_tautologies:                   0
% 2.16/1.07  inst_num_prop_implied:                  0
% 2.16/1.07  inst_num_existing_simplified:           0
% 2.16/1.07  inst_num_eq_res_simplified:             0
% 2.16/1.07  inst_num_child_elim:                    0
% 2.16/1.07  inst_num_of_dismatching_blockings:      45
% 2.16/1.07  inst_num_of_non_proper_insts:           876
% 2.16/1.07  inst_num_of_duplicates:                 0
% 2.16/1.07  inst_inst_num_from_inst_to_res:         0
% 2.16/1.07  inst_dismatching_checking_time:         0.
% 2.16/1.07  
% 2.16/1.07  ------ Resolution
% 2.16/1.07  
% 2.16/1.07  res_num_of_clauses:                     0
% 2.16/1.07  res_num_in_passive:                     0
% 2.16/1.07  res_num_in_active:                      0
% 2.16/1.07  res_num_of_loops:                       79
% 2.16/1.07  res_forward_subset_subsumed:            22
% 2.16/1.07  res_backward_subset_subsumed:           0
% 2.16/1.07  res_forward_subsumed:                   0
% 2.16/1.07  res_backward_subsumed:                  0
% 2.16/1.07  res_forward_subsumption_resolution:     0
% 2.16/1.07  res_backward_subsumption_resolution:    0
% 2.16/1.07  res_clause_to_clause_subsumption:       143
% 2.16/1.07  res_orphan_elimination:                 0
% 2.16/1.07  res_tautology_del:                      21
% 2.16/1.07  res_num_eq_res_simplified:              0
% 2.16/1.07  res_num_sel_changes:                    0
% 2.16/1.07  res_moves_from_active_to_pass:          0
% 2.16/1.07  
% 2.16/1.07  ------ Superposition
% 2.16/1.07  
% 2.16/1.07  sup_time_total:                         0.
% 2.16/1.07  sup_time_generating:                    0.
% 2.16/1.07  sup_time_sim_full:                      0.
% 2.16/1.07  sup_time_sim_immed:                     0.
% 2.16/1.07  
% 2.16/1.07  sup_num_of_clauses:                     61
% 2.16/1.07  sup_num_in_active:                      43
% 2.16/1.07  sup_num_in_passive:                     18
% 2.16/1.07  sup_num_of_loops:                       58
% 2.16/1.07  sup_fw_superposition:                   36
% 2.16/1.07  sup_bw_superposition:                   38
% 2.16/1.07  sup_immediate_simplified:               3
% 2.16/1.07  sup_given_eliminated:                   0
% 2.16/1.07  comparisons_done:                       0
% 2.16/1.07  comparisons_avoided:                    33
% 2.16/1.07  
% 2.16/1.07  ------ Simplifications
% 2.16/1.07  
% 2.16/1.07  
% 2.16/1.07  sim_fw_subset_subsumed:                 3
% 2.16/1.07  sim_bw_subset_subsumed:                 10
% 2.16/1.07  sim_fw_subsumed:                        0
% 2.16/1.07  sim_bw_subsumed:                        0
% 2.16/1.07  sim_fw_subsumption_res:                 0
% 2.16/1.07  sim_bw_subsumption_res:                 0
% 2.16/1.07  sim_tautology_del:                      1
% 2.16/1.07  sim_eq_tautology_del:                   3
% 2.16/1.07  sim_eq_res_simp:                        0
% 2.16/1.07  sim_fw_demodulated:                     0
% 2.16/1.07  sim_bw_demodulated:                     13
% 2.16/1.07  sim_light_normalised:                   0
% 2.16/1.07  sim_joinable_taut:                      0
% 2.16/1.07  sim_joinable_simp:                      0
% 2.16/1.07  sim_ac_normalised:                      0
% 2.16/1.07  sim_smt_subsumption:                    0
% 2.16/1.07  
%------------------------------------------------------------------------------
