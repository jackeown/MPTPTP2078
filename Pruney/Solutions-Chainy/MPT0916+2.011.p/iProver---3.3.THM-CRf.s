%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:13 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 802 expanded)
%              Number of clauses        :   61 ( 222 expanded)
%              Number of leaves         :   12 ( 258 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (4114 expanded)
%              Number of equality atoms :  124 ( 265 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f27,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f26,f25,f24,f23])).

fof(f43,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f8,axiom,(
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

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f42,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f45,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f34])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_453,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_457,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1596,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_457])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_620,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_726,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r2_hidden(k2_mcart_1(sK7),X0)
    | ~ r2_hidden(k2_mcart_1(sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | r2_hidden(k2_mcart_1(sK7),sK3) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1143,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_160,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1201,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_1203,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1318,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_4,c_15])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_882,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_7,c_12])).

cnf(c_888,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(resolution,[status(thm)],[c_882,c_6])).

cnf(c_1405,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK2) ),
    inference(resolution,[status(thm)],[c_1318,c_888])).

cnf(c_1514,plain,
    ( ~ v1_xboole_0(sK2) ),
    inference(resolution,[status(thm)],[c_1405,c_0])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1322,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK1) ),
    inference(resolution,[status(thm)],[c_4,c_16])).

cnf(c_889,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) ),
    inference(resolution,[status(thm)],[c_882,c_7])).

cnf(c_1417,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK1) ),
    inference(resolution,[status(thm)],[c_1322,c_889])).

cnf(c_1520,plain,
    ( ~ v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_1417,c_0])).

cnf(c_2123,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_2125,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_2131,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_2133,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_2245,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203,c_1514,c_1520,c_2125,c_2133])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_458,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1827,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_458])).

cnf(c_2139,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1827,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203,c_1514,c_1520,c_2125,c_2133])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_455,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2143,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2139,c_455])).

cnf(c_21,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_621,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_456,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_988,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_456])).

cnf(c_1291,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203])).

cnf(c_1296,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_455])).

cnf(c_623,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_624,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_750,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_754,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_1373,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1296,c_21,c_624,c_754])).

cnf(c_1374,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1373])).

cnf(c_2142,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2139,c_1374])).

cnf(c_2161,plain,
    ( r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_21,c_3,c_621,c_1514,c_1520,c_2125,c_2133,c_2142])).

cnf(c_2248,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2245,c_2161])).

cnf(c_751,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_752,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2248,c_752,c_624,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.22/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.99  
% 3.22/0.99  ------  iProver source info
% 3.22/0.99  
% 3.22/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.99  git: non_committed_changes: false
% 3.22/0.99  git: last_make_outside_of_git: false
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  ------ Parsing...
% 3.22/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.99  ------ Proving...
% 3.22/0.99  ------ Problem Properties 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  clauses                                 17
% 3.22/0.99  conjectures                             6
% 3.22/0.99  EPR                                     3
% 3.22/0.99  Horn                                    13
% 3.22/0.99  unary                                   6
% 3.22/0.99  binary                                  6
% 3.22/0.99  lits                                    39
% 3.22/0.99  lits eq                                 12
% 3.22/0.99  fd_pure                                 0
% 3.22/0.99  fd_pseudo                               0
% 3.22/0.99  fd_cond                                 3
% 3.22/0.99  fd_pseudo_cond                          0
% 3.22/0.99  AC symbols                              0
% 3.22/0.99  
% 3.22/0.99  ------ Input Options Time Limit: Unbounded
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  Current options:
% 3.22/0.99  ------ 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ Proving...
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS status Theorem for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  fof(f9,conjecture,(
% 3.22/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f10,negated_conjecture,(
% 3.22/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.22/0.99    inference(negated_conjecture,[],[f9])).
% 3.22/0.99  
% 3.22/0.99  fof(f19,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f10])).
% 3.22/0.99  
% 3.22/0.99  fof(f20,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.22/0.99    inference(flattening,[],[f19])).
% 3.22/0.99  
% 3.22/0.99  fof(f26,plain,(
% 3.22/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f25,plain,(
% 3.22/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f24,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f23,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f27,plain,(
% 3.22/0.99    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f26,f25,f24,f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f43,plain,(
% 3.22/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f6,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f34,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f6])).
% 3.22/0.99  
% 3.22/0.99  fof(f50,plain,(
% 3.22/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 3.22/0.99    inference(definition_unfolding,[],[f43,f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f8,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f18,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.22/0.99    inference(ennf_transformation,[],[f8])).
% 3.22/0.99  
% 3.22/0.99  fof(f38,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f18])).
% 3.22/0.99  
% 3.22/0.99  fof(f47,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(definition_unfolding,[],[f38,f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f42,plain,(
% 3.22/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f44,plain,(
% 3.22/0.99    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f49,plain,(
% 3.22/0.99    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 3.22/0.99    inference(definition_unfolding,[],[f44,f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f3,axiom,(
% 3.22/0.99    v1_xboole_0(k1_xboole_0)),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f31,plain,(
% 3.22/0.99    v1_xboole_0(k1_xboole_0)),
% 3.22/0.99    inference(cnf_transformation,[],[f3])).
% 3.22/0.99  
% 3.22/0.99  fof(f7,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f17,plain,(
% 3.22/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.22/0.99    inference(ennf_transformation,[],[f7])).
% 3.22/0.99  
% 3.22/0.99  fof(f36,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f17])).
% 3.22/0.99  
% 3.22/0.99  fof(f4,axiom,(
% 3.22/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f15,plain,(
% 3.22/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f4])).
% 3.22/0.99  
% 3.22/0.99  fof(f32,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f15])).
% 3.22/0.99  
% 3.22/0.99  fof(f1,axiom,(
% 3.22/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f12,plain,(
% 3.22/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.22/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.22/0.99  
% 3.22/0.99  fof(f13,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f12])).
% 3.22/0.99  
% 3.22/0.99  fof(f28,plain,(
% 3.22/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f13])).
% 3.22/0.99  
% 3.22/0.99  fof(f41,plain,(
% 3.22/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f35,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f17])).
% 3.22/0.99  
% 3.22/0.99  fof(f40,plain,(
% 3.22/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f39,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f18])).
% 3.22/0.99  
% 3.22/0.99  fof(f46,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(definition_unfolding,[],[f39,f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f45,plain,(
% 3.22/0.99    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f37,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f18])).
% 3.22/0.99  
% 3.22/0.99  fof(f48,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(definition_unfolding,[],[f37,f34])).
% 3.22/0.99  
% 3.22/0.99  cnf(c_13,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_453,plain,
% 3.22/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.22/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.22/0.99      | k1_xboole_0 = X3
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | k1_xboole_0 = X1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_457,plain,
% 3.22/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1596,plain,
% 3.22/0.99      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 3.22/0.99      | sK3 = k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_453,c_457]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_14,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_12,negated_conjecture,
% 3.22/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3,plain,
% 3.22/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.22/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.22/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_620,plain,
% 3.22/0.99      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 3.22/0.99      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.99      | ~ r2_hidden(X2,X0)
% 3.22/0.99      | r2_hidden(X2,X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_726,plain,
% 3.22/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.22/0.99      | r2_hidden(k2_mcart_1(sK7),X0)
% 3.22/0.99      | ~ r2_hidden(k2_mcart_1(sK7),sK6) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1013,plain,
% 3.22/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
% 3.22/0.99      | ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 3.22/0.99      | r2_hidden(k2_mcart_1(sK7),sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_0,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1143,plain,
% 3.22/0.99      ( ~ r2_hidden(k2_mcart_1(sK7),sK3) | ~ v1_xboole_0(sK3) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_160,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1201,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_160]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1203,plain,
% 3.22/0.99      ( v1_xboole_0(sK3)
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/0.99      | sK3 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1201]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_15,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1318,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,sK5) | r2_hidden(X0,sK2) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_4,c_15]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.22/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_882,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_7,c_12]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_888,plain,
% 3.22/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_882,c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1405,plain,
% 3.22/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK2) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1318,c_888]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1514,plain,
% 3.22/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1405,c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_16,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1322,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK1) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_4,c_16]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_889,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_882,c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1417,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK1) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1322,c_889]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1520,plain,
% 3.22/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1417,c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2123,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_160]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2125,plain,
% 3.22/0.99      ( v1_xboole_0(sK1)
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/0.99      | sK1 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2131,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_160]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2133,plain,
% 3.22/0.99      ( v1_xboole_0(sK2)
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/0.99      | sK2 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2131]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2245,plain,
% 3.22/0.99      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_1596,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203,c_1514,
% 3.22/0.99                 c_1520,c_2125,c_2133]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.22/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.22/0.99      | k1_xboole_0 = X3
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | k1_xboole_0 = X1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_458,plain,
% 3.22/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1827,plain,
% 3.22/0.99      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 3.22/0.99      | sK3 = k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_453,c_458]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2139,plain,
% 3.22/0.99      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_1827,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203,c_1514,
% 3.22/0.99                 c_1520,c_2125,c_2133]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_11,negated_conjecture,
% 3.22/0.99      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 3.22/0.99      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 3.22/0.99      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 3.22/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_455,plain,
% 3.22/0.99      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2143,plain,
% 3.22/0.99      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_2139,c_455]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_21,plain,
% 3.22/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_621,plain,
% 3.22/0.99      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
% 3.22/0.99      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_10,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.22/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.22/0.99      | k1_xboole_0 = X3
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | k1_xboole_0 = X1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_456,plain,
% 3.22/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = X2
% 3.22/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_988,plain,
% 3.22/0.99      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.22/0.99      | sK3 = k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_453,c_456]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1291,plain,
% 3.22/0.99      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_988,c_14,c_12,c_3,c_620,c_1013,c_1143,c_1203]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1296,plain,
% 3.22/0.99      ( sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 3.22/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1291,c_455]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_623,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 3.22/0.99      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_624,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 3.22/0.99      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_750,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 3.22/0.99      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_754,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 3.22/0.99      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1373,plain,
% 3.22/0.99      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | sK1 = k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_1296,c_21,c_624,c_754]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1374,plain,
% 3.22/0.99      ( sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 3.22/0.99      inference(renaming,[status(thm)],[c_1373]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2142,plain,
% 3.22/0.99      ( sK2 = k1_xboole_0
% 3.22/0.99      | sK1 = k1_xboole_0
% 3.22/0.99      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 3.22/0.99      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_2139,c_1374]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2161,plain,
% 3.22/0.99      ( r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_2143,c_21,c_3,c_621,c_1514,c_1520,c_2125,c_2133,
% 3.22/0.99                 c_2142]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2248,plain,
% 3.22/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_2245,c_2161]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_751,plain,
% 3.22/0.99      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 3.22/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_752,plain,
% 3.22/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.22/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(contradiction,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(minisat,[status(thm)],[c_2248,c_752,c_624,c_21]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ Selected
% 3.22/0.99  
% 3.22/0.99  total_time:                             0.112
% 3.22/0.99  
%------------------------------------------------------------------------------
