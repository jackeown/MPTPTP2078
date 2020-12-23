%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:11 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 485 expanded)
%              Number of clauses        :   80 ( 186 expanded)
%              Number of leaves         :   16 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  405 (2161 expanded)
%              Number of equality atoms :  194 ( 359 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f30,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f29,f28,f27,f26])).

fof(f49,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f50,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f51,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1470,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1475,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7315,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1470,c_1475])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_250,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_251,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_252,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_254,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3)
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_1140,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1161,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1622,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1623,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1681,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1682,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1484,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_1466,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1996,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1466])).

cnf(c_1144,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2052,plain,
    ( X0 != sK3
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_2057,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_1141,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7673,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_7674,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7673])).

cnf(c_8073,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7315,c_24,c_254,c_1161,c_1623,c_1682,c_1996,c_2057,c_7674])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1474,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3800,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1470,c_1474])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1473,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1991,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1470,c_1473])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1472,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3066,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_1472])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1625,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1626,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_1701,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1705,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1701])).

cnf(c_3069,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3066,c_24,c_1626,c_1705])).

cnf(c_3070,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3069])).

cnf(c_5912,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3800,c_3070])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_265,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_266,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_267,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_269,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK2)
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_280,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_281,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_282,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1702,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1703,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_1905,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1906,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1905])).

cnf(c_1919,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1920,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_2375,plain,
    ( X0 != sK2
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_2380,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_2401,plain,
    ( X0 != sK1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_2406,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_8727,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_8728,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8727])).

cnf(c_8769,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_8770,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8769])).

cnf(c_8893,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5912,c_24,c_254,c_269,c_284,c_1161,c_1623,c_1626,c_1682,c_1703,c_1705,c_1906,c_1920,c_1996,c_2057,c_2380,c_2406,c_7674,c_8728,c_8770])).

cnf(c_8898,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8073,c_8893])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8898,c_8770,c_8728,c_2406,c_2380,c_1996,c_1920,c_1906,c_1705,c_1703,c_1626,c_1623,c_1161,c_284,c_269,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.98  
% 2.99/0.98  ------  iProver source info
% 2.99/0.98  
% 2.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.98  git: non_committed_changes: false
% 2.99/0.98  git: last_make_outside_of_git: false
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     num_symb
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.98  --inst_passive_queues_freq              [25;2]
% 2.99/0.98  --inst_dismatching                      true
% 2.99/0.98  --inst_eager_unprocessed_to_passive     true
% 2.99/0.98  --inst_prop_sim_given                   true
% 2.99/0.98  --inst_prop_sim_new                     false
% 2.99/0.98  --inst_subs_new                         false
% 2.99/0.98  --inst_eq_res_simp                      false
% 2.99/0.98  --inst_subs_given                       false
% 2.99/0.98  --inst_orphan_elimination               true
% 2.99/0.98  --inst_learning_loop_flag               true
% 2.99/0.98  --inst_learning_start                   3000
% 2.99/0.98  --inst_learning_factor                  2
% 2.99/0.98  --inst_start_prop_sim_after_learn       3
% 2.99/0.98  --inst_sel_renew                        solver
% 2.99/0.98  --inst_lit_activity_flag                true
% 2.99/0.98  --inst_restr_to_given                   false
% 2.99/0.98  --inst_activity_threshold               500
% 2.99/0.98  --inst_out_proof                        true
% 2.99/0.98  
% 2.99/0.98  ------ Resolution Options
% 2.99/0.98  
% 2.99/0.98  --resolution_flag                       true
% 2.99/0.98  --res_lit_sel                           adaptive
% 2.99/0.98  --res_lit_sel_side                      none
% 2.99/0.98  --res_ordering                          kbo
% 2.99/0.98  --res_to_prop_solver                    active
% 2.99/0.98  --res_prop_simpl_new                    false
% 2.99/0.98  --res_prop_simpl_given                  true
% 2.99/0.98  --res_passive_queue_type                priority_queues
% 2.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.98  --res_passive_queues_freq               [15;5]
% 2.99/0.98  --res_forward_subs                      full
% 2.99/0.98  --res_backward_subs                     full
% 2.99/0.98  --res_forward_subs_resolution           true
% 2.99/0.98  --res_backward_subs_resolution          true
% 2.99/0.98  --res_orphan_elimination                true
% 2.99/0.98  --res_time_limit                        2.
% 2.99/0.98  --res_out_proof                         true
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Options
% 2.99/0.98  
% 2.99/0.98  --superposition_flag                    true
% 2.99/0.98  --sup_passive_queue_type                priority_queues
% 2.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.98  --demod_completeness_check              fast
% 2.99/0.98  --demod_use_ground                      true
% 2.99/0.98  --sup_to_prop_solver                    passive
% 2.99/0.98  --sup_prop_simpl_new                    true
% 2.99/0.98  --sup_prop_simpl_given                  true
% 2.99/0.98  --sup_fun_splitting                     false
% 2.99/0.98  --sup_smt_interval                      50000
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Simplification Setup
% 2.99/0.98  
% 2.99/0.98  --sup_indices_passive                   []
% 2.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_full_bw                           [BwDemod]
% 2.99/0.98  --sup_immed_triv                        [TrivRules]
% 2.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_immed_bw_main                     []
% 2.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  
% 2.99/0.98  ------ Combination Options
% 2.99/0.98  
% 2.99/0.98  --comb_res_mult                         3
% 2.99/0.98  --comb_sup_mult                         2
% 2.99/0.98  --comb_inst_mult                        10
% 2.99/0.98  
% 2.99/0.98  ------ Debug Options
% 2.99/0.98  
% 2.99/0.98  --dbg_backtrace                         false
% 2.99/0.98  --dbg_dump_prop_clauses                 false
% 2.99/0.98  --dbg_dump_prop_clauses_file            -
% 2.99/0.98  --dbg_out_stat                          false
% 2.99/0.98  ------ Parsing...
% 2.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.98  ------ Proving...
% 2.99/0.98  ------ Problem Properties 
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  clauses                                 19
% 2.99/0.98  conjectures                             6
% 2.99/0.98  EPR                                     3
% 2.99/0.98  Horn                                    14
% 2.99/0.98  unary                                   6
% 2.99/0.98  binary                                  6
% 2.99/0.98  lits                                    45
% 2.99/0.98  lits eq                                 12
% 2.99/0.98  fd_pure                                 0
% 2.99/0.98  fd_pseudo                               0
% 2.99/0.98  fd_cond                                 3
% 2.99/0.98  fd_pseudo_cond                          0
% 2.99/0.98  AC symbols                              0
% 2.99/0.98  
% 2.99/0.98  ------ Schedule dynamic 5 is on 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  Current options:
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     none
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       false
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ Proving...
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS status Theorem for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  fof(f10,conjecture,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f11,negated_conjecture,(
% 2.99/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.99/0.99    inference(negated_conjecture,[],[f10])).
% 2.99/0.99  
% 2.99/0.99  fof(f18,plain,(
% 2.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f11])).
% 2.99/0.99  
% 2.99/0.99  fof(f19,plain,(
% 2.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.99/0.99    inference(flattening,[],[f18])).
% 2.99/0.99  
% 2.99/0.99  fof(f29,plain,(
% 2.99/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f28,plain,(
% 2.99/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f27,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f26,plain,(
% 2.99/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f30,plain,(
% 2.99/0.99    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f29,f28,f27,f26])).
% 2.99/0.99  
% 2.99/0.99  fof(f49,plain,(
% 2.99/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f7,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f40,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f7])).
% 2.99/0.99  
% 2.99/0.99  fof(f56,plain,(
% 2.99/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.99/0.99    inference(definition_unfolding,[],[f49,f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f9,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f17,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.99/0.99    inference(ennf_transformation,[],[f9])).
% 2.99/0.99  
% 2.99/0.99  fof(f45,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(cnf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f52,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(definition_unfolding,[],[f45,f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f50,plain,(
% 2.99/0.99    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f55,plain,(
% 2.99/0.99    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.99/0.99    inference(definition_unfolding,[],[f50,f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f4,axiom,(
% 2.99/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f12,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f4])).
% 2.99/0.99  
% 2.99/0.99  fof(f37,plain,(
% 2.99/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f12])).
% 2.99/0.99  
% 2.99/0.99  fof(f48,plain,(
% 2.99/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f8,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f16,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f8])).
% 2.99/0.99  
% 2.99/0.99  fof(f42,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f1,axiom,(
% 2.99/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f20,plain,(
% 2.99/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.99/0.99    inference(nnf_transformation,[],[f1])).
% 2.99/0.99  
% 2.99/0.99  fof(f21,plain,(
% 2.99/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.99/0.99    inference(rectify,[],[f20])).
% 2.99/0.99  
% 2.99/0.99  fof(f22,plain,(
% 2.99/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f23,plain,(
% 2.99/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.99/0.99  
% 2.99/0.99  fof(f31,plain,(
% 2.99/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f32,plain,(
% 2.99/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f2,axiom,(
% 2.99/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f33,plain,(
% 2.99/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f2])).
% 2.99/0.99  
% 2.99/0.99  fof(f6,axiom,(
% 2.99/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f15,plain,(
% 2.99/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.99/0.99    inference(ennf_transformation,[],[f6])).
% 2.99/0.99  
% 2.99/0.99  fof(f39,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f15])).
% 2.99/0.99  
% 2.99/0.99  fof(f44,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(cnf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f53,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(definition_unfolding,[],[f44,f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f43,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(cnf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f54,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(definition_unfolding,[],[f43,f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f51,plain,(
% 2.99/0.99    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f41,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f47,plain,(
% 2.99/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f46,plain,(
% 2.99/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  cnf(c_16,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1470,plain,
% 2.99/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_11,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.99/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.99/0.99      | k1_xboole_0 = X3
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | k1_xboole_0 = X1 ),
% 2.99/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1475,plain,
% 2.99/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.99/0.99      | k1_xboole_0 = X0
% 2.99/0.99      | k1_xboole_0 = X1
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7315,plain,
% 2.99/0.99      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.99/0.99      | sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1470,c_1475]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_15,negated_conjecture,
% 2.99/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_24,plain,
% 2.99/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/0.99      | ~ v1_xboole_0(X1)
% 2.99/0.99      | v1_xboole_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_17,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_250,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(X1)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 2.99/0.99      | sK6 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_251,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(sK6)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_250]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_252,plain,
% 2.99/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 2.99/0.99      | v1_xboole_0(X0) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_254,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3)
% 2.99/0.99      | v1_xboole_0(sK6) = iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_252]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1140,plain,( X0 = X0 ),theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1161,plain,
% 2.99/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_9,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.99/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1622,plain,
% 2.99/0.99      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.99/0.99      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1623,plain,
% 2.99/0.99      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
% 2.99/0.99      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1681,plain,
% 2.99/0.99      ( ~ r2_hidden(k2_mcart_1(sK7),sK6) | ~ v1_xboole_0(sK6) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1682,plain,
% 2.99/0.99      ( r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_0,plain,
% 2.99/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1484,plain,
% 2.99/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.99/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2,plain,
% 2.99/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8,plain,
% 2.99/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_224,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_225,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_224]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1466,plain,
% 2.99/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1996,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1484,c_1466]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1144,plain,
% 2.99/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2052,plain,
% 2.99/0.99      ( X0 != sK3 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1144]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2057,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
% 2.99/0.99      | k1_xboole_0 != sK3 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2052]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1141,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7673,plain,
% 2.99/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7674,plain,
% 2.99/0.99      ( sK3 != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 = sK3
% 2.99/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_7673]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8073,plain,
% 2.99/0.99      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_7315,c_24,c_254,c_1161,c_1623,c_1682,c_1996,c_2057,
% 2.99/0.99                 c_7674]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_12,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.99/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.99/0.99      | k1_xboole_0 = X3
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | k1_xboole_0 = X1 ),
% 2.99/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1474,plain,
% 2.99/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.99/0.99      | k1_xboole_0 = X0
% 2.99/0.99      | k1_xboole_0 = X1
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3800,plain,
% 2.99/0.99      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.99/0.99      | sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1470,c_1474]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_13,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.99/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.99/0.99      | k1_xboole_0 = X3
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | k1_xboole_0 = X1 ),
% 2.99/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1473,plain,
% 2.99/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.99/0.99      | k1_xboole_0 = X0
% 2.99/0.99      | k1_xboole_0 = X1
% 2.99/0.99      | k1_xboole_0 = X2
% 2.99/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1991,plain,
% 2.99/0.99      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.99/0.99      | sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1470,c_1473]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_14,negated_conjecture,
% 2.99/0.99      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.99/0.99      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.99/0.99      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.99/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1472,plain,
% 2.99/0.99      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.99/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.99/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3066,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0
% 2.99/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.99/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.99/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1991,c_1472]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_10,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.99/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1625,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.99/0.99      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1626,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.99/0.99      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1701,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.99/0.99      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1705,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.99/0.99      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1701]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3069,plain,
% 2.99/0.99      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.99/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.99/0.99      | sK1 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK3 = k1_xboole_0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3066,c_24,c_1626,c_1705]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3070,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0
% 2.99/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.99/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_3069]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5912,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0
% 2.99/0.99      | sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0
% 2.99/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.99/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3800,c_3070]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_18,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_265,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(X1)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 2.99/0.99      | sK5 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_266,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(sK5)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_265]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_267,plain,
% 2.99/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 2.99/0.99      | v1_xboole_0(X0) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_269,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK2)
% 2.99/0.99      | v1_xboole_0(sK5) = iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_19,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_280,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(X1)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 2.99/0.99      | sK4 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_281,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(sK4)
% 2.99/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_282,plain,
% 2.99/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 2.99/0.99      | v1_xboole_0(X0) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_284,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
% 2.99/0.99      | v1_xboole_0(sK4) = iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_282]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1702,plain,
% 2.99/0.99      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.99/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1703,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.99/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1702]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1905,plain,
% 2.99/0.99      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.99/0.99      | ~ v1_xboole_0(sK4) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1906,plain,
% 2.99/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1905]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1919,plain,
% 2.99/0.99      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
% 2.99/0.99      | ~ v1_xboole_0(sK5) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1920,plain,
% 2.99/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK5) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2375,plain,
% 2.99/0.99      ( X0 != sK2 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1144]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2380,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK2)
% 2.99/0.99      | k1_xboole_0 != sK2 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2375]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2401,plain,
% 2.99/0.99      ( X0 != sK1 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1144]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2406,plain,
% 2.99/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
% 2.99/0.99      | k1_xboole_0 != sK1 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2401]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8727,plain,
% 2.99/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8728,plain,
% 2.99/0.99      ( sK2 != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 = sK2
% 2.99/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_8727]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8769,plain,
% 2.99/0.99      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1141]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8770,plain,
% 2.99/0.99      ( sK1 != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 = sK1
% 2.99/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_8769]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8893,plain,
% 2.99/0.99      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_5912,c_24,c_254,c_269,c_284,c_1161,c_1623,c_1626,
% 2.99/0.99                 c_1682,c_1703,c_1705,c_1906,c_1920,c_1996,c_2057,c_2380,
% 2.99/0.99                 c_2406,c_7674,c_8728,c_8770]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8898,plain,
% 2.99/0.99      ( sK2 = k1_xboole_0
% 2.99/0.99      | sK1 = k1_xboole_0
% 2.99/0.99      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_8073,c_8893]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(contradiction,plain,
% 2.99/0.99      ( $false ),
% 2.99/0.99      inference(minisat,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_8898,c_8770,c_8728,c_2406,c_2380,c_1996,c_1920,c_1906,
% 2.99/0.99                 c_1705,c_1703,c_1626,c_1623,c_1161,c_284,c_269,c_24]) ).
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  ------                               Statistics
% 2.99/0.99  
% 2.99/0.99  ------ General
% 2.99/0.99  
% 2.99/0.99  abstr_ref_over_cycles:                  0
% 2.99/0.99  abstr_ref_under_cycles:                 0
% 2.99/0.99  gc_basic_clause_elim:                   0
% 2.99/0.99  forced_gc_time:                         0
% 2.99/0.99  parsing_time:                           0.007
% 2.99/0.99  unif_index_cands_time:                  0.
% 2.99/0.99  unif_index_add_time:                    0.
% 2.99/0.99  orderings_time:                         0.
% 2.99/0.99  out_proof_time:                         0.01
% 2.99/0.99  total_time:                             0.274
% 2.99/0.99  num_of_symbols:                         52
% 2.99/0.99  num_of_terms:                           11730
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing
% 2.99/0.99  
% 2.99/0.99  num_of_splits:                          0
% 2.99/0.99  num_of_split_atoms:                     0
% 2.99/0.99  num_of_reused_defs:                     0
% 2.99/0.99  num_eq_ax_congr_red:                    13
% 2.99/0.99  num_of_sem_filtered_clauses:            1
% 2.99/0.99  num_of_subtypes:                        0
% 2.99/0.99  monotx_restored_types:                  0
% 2.99/0.99  sat_num_of_epr_types:                   0
% 2.99/0.99  sat_num_of_non_cyclic_types:            0
% 2.99/0.99  sat_guarded_non_collapsed_types:        0
% 2.99/0.99  num_pure_diseq_elim:                    0
% 2.99/0.99  simp_replaced_by:                       0
% 2.99/0.99  res_preprocessed:                       100
% 2.99/0.99  prep_upred:                             0
% 2.99/0.99  prep_unflattend:                        50
% 2.99/0.99  smt_new_axioms:                         0
% 2.99/0.99  pred_elim_cands:                        3
% 2.99/0.99  pred_elim:                              1
% 2.99/0.99  pred_elim_cl:                           1
% 2.99/0.99  pred_elim_cycles:                       3
% 2.99/0.99  merged_defs:                            0
% 2.99/0.99  merged_defs_ncl:                        0
% 2.99/0.99  bin_hyper_res:                          0
% 2.99/0.99  prep_cycles:                            4
% 2.99/0.99  pred_elim_time:                         0.012
% 2.99/0.99  splitting_time:                         0.
% 2.99/0.99  sem_filter_time:                        0.
% 2.99/0.99  monotx_time:                            0.
% 2.99/0.99  subtype_inf_time:                       0.
% 2.99/0.99  
% 2.99/0.99  ------ Problem properties
% 2.99/0.99  
% 2.99/0.99  clauses:                                19
% 2.99/0.99  conjectures:                            6
% 2.99/0.99  epr:                                    3
% 2.99/0.99  horn:                                   14
% 2.99/0.99  ground:                                 6
% 2.99/0.99  unary:                                  6
% 2.99/0.99  binary:                                 6
% 2.99/0.99  lits:                                   45
% 2.99/0.99  lits_eq:                                12
% 2.99/0.99  fd_pure:                                0
% 2.99/0.99  fd_pseudo:                              0
% 2.99/0.99  fd_cond:                                3
% 2.99/0.99  fd_pseudo_cond:                         0
% 2.99/0.99  ac_symbols:                             0
% 2.99/0.99  
% 2.99/0.99  ------ Propositional Solver
% 2.99/0.99  
% 2.99/0.99  prop_solver_calls:                      29
% 2.99/0.99  prop_fast_solver_calls:                 779
% 2.99/0.99  smt_solver_calls:                       0
% 2.99/0.99  smt_fast_solver_calls:                  0
% 2.99/0.99  prop_num_of_clauses:                    3845
% 2.99/0.99  prop_preprocess_simplified:             10447
% 2.99/0.99  prop_fo_subsumed:                       9
% 2.99/0.99  prop_solver_time:                       0.
% 2.99/0.99  smt_solver_time:                        0.
% 2.99/0.99  smt_fast_solver_time:                   0.
% 2.99/0.99  prop_fast_solver_time:                  0.
% 2.99/0.99  prop_unsat_core_time:                   0.
% 2.99/0.99  
% 2.99/0.99  ------ QBF
% 2.99/0.99  
% 2.99/0.99  qbf_q_res:                              0
% 2.99/0.99  qbf_num_tautologies:                    0
% 2.99/0.99  qbf_prep_cycles:                        0
% 2.99/0.99  
% 2.99/0.99  ------ BMC1
% 2.99/0.99  
% 2.99/0.99  bmc1_current_bound:                     -1
% 2.99/0.99  bmc1_last_solved_bound:                 -1
% 2.99/0.99  bmc1_unsat_core_size:                   -1
% 2.99/0.99  bmc1_unsat_core_parents_size:           -1
% 2.99/0.99  bmc1_merge_next_fun:                    0
% 2.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation
% 2.99/0.99  
% 2.99/0.99  inst_num_of_clauses:                    1739
% 2.99/0.99  inst_num_in_passive:                    953
% 2.99/0.99  inst_num_in_active:                     219
% 2.99/0.99  inst_num_in_unprocessed:                567
% 2.99/0.99  inst_num_of_loops:                      220
% 2.99/0.99  inst_num_of_learning_restarts:          0
% 2.99/0.99  inst_num_moves_active_passive:          0
% 2.99/0.99  inst_lit_activity:                      0
% 2.99/0.99  inst_lit_activity_moves:                0
% 2.99/0.99  inst_num_tautologies:                   0
% 2.99/0.99  inst_num_prop_implied:                  0
% 2.99/0.99  inst_num_existing_simplified:           0
% 2.99/0.99  inst_num_eq_res_simplified:             0
% 2.99/0.99  inst_num_child_elim:                    0
% 2.99/0.99  inst_num_of_dismatching_blockings:      5
% 2.99/0.99  inst_num_of_non_proper_insts:           784
% 2.99/0.99  inst_num_of_duplicates:                 0
% 2.99/0.99  inst_inst_num_from_inst_to_res:         0
% 2.99/0.99  inst_dismatching_checking_time:         0.
% 2.99/0.99  
% 2.99/0.99  ------ Resolution
% 2.99/0.99  
% 2.99/0.99  res_num_of_clauses:                     0
% 2.99/0.99  res_num_in_passive:                     0
% 2.99/0.99  res_num_in_active:                      0
% 2.99/0.99  res_num_of_loops:                       104
% 2.99/0.99  res_forward_subset_subsumed:            93
% 2.99/0.99  res_backward_subset_subsumed:           0
% 2.99/0.99  res_forward_subsumed:                   0
% 2.99/0.99  res_backward_subsumed:                  0
% 2.99/0.99  res_forward_subsumption_resolution:     0
% 2.99/0.99  res_backward_subsumption_resolution:    0
% 2.99/0.99  res_clause_to_clause_subsumption:       46
% 2.99/0.99  res_orphan_elimination:                 0
% 2.99/0.99  res_tautology_del:                      8
% 2.99/0.99  res_num_eq_res_simplified:              0
% 2.99/0.99  res_num_sel_changes:                    0
% 2.99/0.99  res_moves_from_active_to_pass:          0
% 2.99/0.99  
% 2.99/0.99  ------ Superposition
% 2.99/0.99  
% 2.99/0.99  sup_time_total:                         0.
% 2.99/0.99  sup_time_generating:                    0.
% 2.99/0.99  sup_time_sim_full:                      0.
% 2.99/0.99  sup_time_sim_immed:                     0.
% 2.99/0.99  
% 2.99/0.99  sup_num_of_clauses:                     55
% 2.99/0.99  sup_num_in_active:                      43
% 2.99/0.99  sup_num_in_passive:                     12
% 2.99/0.99  sup_num_of_loops:                       42
% 2.99/0.99  sup_fw_superposition:                   16
% 2.99/0.99  sup_bw_superposition:                   24
% 2.99/0.99  sup_immediate_simplified:               0
% 2.99/0.99  sup_given_eliminated:                   0
% 2.99/0.99  comparisons_done:                       0
% 2.99/0.99  comparisons_avoided:                    33
% 2.99/0.99  
% 2.99/0.99  ------ Simplifications
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  sim_fw_subset_subsumed:                 0
% 2.99/0.99  sim_bw_subset_subsumed:                 0
% 2.99/0.99  sim_fw_subsumed:                        0
% 2.99/0.99  sim_bw_subsumed:                        0
% 2.99/0.99  sim_fw_subsumption_res:                 0
% 2.99/0.99  sim_bw_subsumption_res:                 0
% 2.99/0.99  sim_tautology_del:                      7
% 2.99/0.99  sim_eq_tautology_del:                   0
% 2.99/0.99  sim_eq_res_simp:                        0
% 2.99/0.99  sim_fw_demodulated:                     0
% 2.99/0.99  sim_bw_demodulated:                     0
% 2.99/0.99  sim_light_normalised:                   0
% 2.99/0.99  sim_joinable_taut:                      0
% 2.99/0.99  sim_joinable_simp:                      0
% 2.99/0.99  sim_ac_normalised:                      0
% 2.99/0.99  sim_smt_subsumption:                    0
% 2.99/0.99  
%------------------------------------------------------------------------------
