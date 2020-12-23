%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:29 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 762 expanded)
%              Number of clauses        :   37 ( 114 expanded)
%              Number of leaves         :   16 ( 202 expanded)
%              Depth                    :   25
%              Number of atoms          :  341 (2316 expanded)
%              Number of equality atoms :  136 ( 941 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK9,sK8) != sK7
      & r2_hidden(sK8,sK6)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_2(sK9,sK6,k1_tarski(sK7))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_funct_1(sK9,sK8) != sK7
    & r2_hidden(sK8,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f45])).

fof(f86,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f91])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f92])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f93])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f94])).

fof(f103,plain,(
    v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f86,f95])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f87,f95])).

fof(f85,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f95])).

fof(f109,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f95])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f98])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f107])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f43])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK9 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_33])).

cnf(c_450,plain,
    ( ~ v1_funct_2(sK9,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK9,X2),X1)
    | ~ v1_funct_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_454,plain,
    ( r2_hidden(k1_funct_1(sK9,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK9,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_35])).

cnf(c_455,plain,
    ( ~ v1_funct_2(sK9,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK9,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK9,X0),X2)
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X1
    | sK9 != sK9
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_455])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1076,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(equality_resolution_simp,[status(thm)],[c_483])).

cnf(c_2541,plain,
    ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2790,plain,
    ( r2_hidden(k1_funct_1(sK9,sK8),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | ~ r2_hidden(sK8,sK6)
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2827,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK8),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | k1_funct_1(sK9,sK8) = sK7 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2857,plain,
    ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_32,c_31,c_2790,c_2827])).

cnf(c_8,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2564,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3121,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2564])).

cnf(c_29,plain,
    ( r2_hidden(sK5(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2543,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2567,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3261,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2567])).

cnf(c_2563,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3405,plain,
    ( sK7 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_2563])).

cnf(c_10651,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0
    | sK5(k4_xboole_0(k1_xboole_0,X0)) = sK7 ),
    inference(superposition,[status(thm)],[c_3261,c_3405])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2568,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3268,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2568])).

cnf(c_11604,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10651,c_3268])).

cnf(c_12389,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3121,c_11604])).

cnf(c_12420,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12389,c_2568])).

cnf(c_12676,plain,
    ( r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12420])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12676,c_3121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.99  
% 2.77/0.99  ------  iProver source info
% 2.77/0.99  
% 2.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.99  git: non_committed_changes: false
% 2.77/0.99  git: last_make_outside_of_git: false
% 2.77/0.99  
% 2.77/0.99  ------ 
% 2.77/0.99  
% 2.77/0.99  ------ Input Options
% 2.77/0.99  
% 2.77/0.99  --out_options                           all
% 2.77/0.99  --tptp_safe_out                         true
% 2.77/0.99  --problem_path                          ""
% 2.77/0.99  --include_path                          ""
% 2.77/0.99  --clausifier                            res/vclausify_rel
% 2.77/0.99  --clausifier_options                    --mode clausify
% 2.77/0.99  --stdin                                 false
% 2.77/0.99  --stats_out                             all
% 2.77/0.99  
% 2.77/0.99  ------ General Options
% 2.77/0.99  
% 2.77/0.99  --fof                                   false
% 2.77/0.99  --time_out_real                         305.
% 2.77/0.99  --time_out_virtual                      -1.
% 2.77/0.99  --symbol_type_check                     false
% 2.77/0.99  --clausify_out                          false
% 2.77/0.99  --sig_cnt_out                           false
% 2.77/0.99  --trig_cnt_out                          false
% 2.77/0.99  --trig_cnt_out_tolerance                1.
% 2.77/0.99  --trig_cnt_out_sk_spl                   false
% 2.77/0.99  --abstr_cl_out                          false
% 2.77/0.99  
% 2.77/0.99  ------ Global Options
% 2.77/0.99  
% 2.77/0.99  --schedule                              default
% 2.77/0.99  --add_important_lit                     false
% 2.77/0.99  --prop_solver_per_cl                    1000
% 2.77/0.99  --min_unsat_core                        false
% 2.77/0.99  --soft_assumptions                      false
% 2.77/0.99  --soft_lemma_size                       3
% 2.77/0.99  --prop_impl_unit_size                   0
% 2.77/0.99  --prop_impl_unit                        []
% 2.77/0.99  --share_sel_clauses                     true
% 2.77/0.99  --reset_solvers                         false
% 2.77/0.99  --bc_imp_inh                            [conj_cone]
% 2.77/0.99  --conj_cone_tolerance                   3.
% 2.77/0.99  --extra_neg_conj                        none
% 2.77/0.99  --large_theory_mode                     true
% 2.77/0.99  --prolific_symb_bound                   200
% 2.77/0.99  --lt_threshold                          2000
% 2.77/0.99  --clause_weak_htbl                      true
% 2.77/0.99  --gc_record_bc_elim                     false
% 2.77/0.99  
% 2.77/0.99  ------ Preprocessing Options
% 2.77/0.99  
% 2.77/0.99  --preprocessing_flag                    true
% 2.77/0.99  --time_out_prep_mult                    0.1
% 2.77/0.99  --splitting_mode                        input
% 2.77/0.99  --splitting_grd                         true
% 2.77/0.99  --splitting_cvd                         false
% 2.77/0.99  --splitting_cvd_svl                     false
% 2.77/0.99  --splitting_nvd                         32
% 2.77/0.99  --sub_typing                            true
% 2.77/0.99  --prep_gs_sim                           true
% 2.77/0.99  --prep_unflatten                        true
% 2.77/0.99  --prep_res_sim                          true
% 2.77/0.99  --prep_upred                            true
% 2.77/0.99  --prep_sem_filter                       exhaustive
% 2.77/0.99  --prep_sem_filter_out                   false
% 2.77/0.99  --pred_elim                             true
% 2.77/0.99  --res_sim_input                         true
% 2.77/0.99  --eq_ax_congr_red                       true
% 2.77/0.99  --pure_diseq_elim                       true
% 2.77/0.99  --brand_transform                       false
% 2.77/0.99  --non_eq_to_eq                          false
% 2.77/0.99  --prep_def_merge                        true
% 2.77/0.99  --prep_def_merge_prop_impl              false
% 2.77/0.99  --prep_def_merge_mbd                    true
% 2.77/0.99  --prep_def_merge_tr_red                 false
% 2.77/0.99  --prep_def_merge_tr_cl                  false
% 2.77/0.99  --smt_preprocessing                     true
% 2.77/0.99  --smt_ac_axioms                         fast
% 2.77/0.99  --preprocessed_out                      false
% 2.77/0.99  --preprocessed_stats                    false
% 2.77/0.99  
% 2.77/0.99  ------ Abstraction refinement Options
% 2.77/0.99  
% 2.77/0.99  --abstr_ref                             []
% 2.77/0.99  --abstr_ref_prep                        false
% 2.77/0.99  --abstr_ref_until_sat                   false
% 2.77/0.99  --abstr_ref_sig_restrict                funpre
% 2.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.99  --abstr_ref_under                       []
% 2.77/0.99  
% 2.77/0.99  ------ SAT Options
% 2.77/0.99  
% 2.77/0.99  --sat_mode                              false
% 2.77/0.99  --sat_fm_restart_options                ""
% 2.77/0.99  --sat_gr_def                            false
% 2.77/0.99  --sat_epr_types                         true
% 2.77/0.99  --sat_non_cyclic_types                  false
% 2.77/0.99  --sat_finite_models                     false
% 2.77/0.99  --sat_fm_lemmas                         false
% 2.77/0.99  --sat_fm_prep                           false
% 2.77/0.99  --sat_fm_uc_incr                        true
% 2.77/0.99  --sat_out_model                         small
% 2.77/0.99  --sat_out_clauses                       false
% 2.77/0.99  
% 2.77/0.99  ------ QBF Options
% 2.77/0.99  
% 2.77/0.99  --qbf_mode                              false
% 2.77/0.99  --qbf_elim_univ                         false
% 2.77/0.99  --qbf_dom_inst                          none
% 2.77/0.99  --qbf_dom_pre_inst                      false
% 2.77/0.99  --qbf_sk_in                             false
% 2.77/0.99  --qbf_pred_elim                         true
% 2.77/0.99  --qbf_split                             512
% 2.77/0.99  
% 2.77/0.99  ------ BMC1 Options
% 2.77/0.99  
% 2.77/0.99  --bmc1_incremental                      false
% 2.77/0.99  --bmc1_axioms                           reachable_all
% 2.77/0.99  --bmc1_min_bound                        0
% 2.77/0.99  --bmc1_max_bound                        -1
% 2.77/0.99  --bmc1_max_bound_default                -1
% 2.77/0.99  --bmc1_symbol_reachability              true
% 2.77/0.99  --bmc1_property_lemmas                  false
% 2.77/0.99  --bmc1_k_induction                      false
% 2.77/0.99  --bmc1_non_equiv_states                 false
% 2.77/0.99  --bmc1_deadlock                         false
% 2.77/0.99  --bmc1_ucm                              false
% 2.77/0.99  --bmc1_add_unsat_core                   none
% 2.77/0.99  --bmc1_unsat_core_children              false
% 2.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.99  --bmc1_out_stat                         full
% 2.77/0.99  --bmc1_ground_init                      false
% 2.77/0.99  --bmc1_pre_inst_next_state              false
% 2.77/0.99  --bmc1_pre_inst_state                   false
% 2.77/0.99  --bmc1_pre_inst_reach_state             false
% 2.77/0.99  --bmc1_out_unsat_core                   false
% 2.77/0.99  --bmc1_aig_witness_out                  false
% 2.77/0.99  --bmc1_verbose                          false
% 2.77/0.99  --bmc1_dump_clauses_tptp                false
% 2.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.99  --bmc1_dump_file                        -
% 2.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.99  --bmc1_ucm_extend_mode                  1
% 2.77/0.99  --bmc1_ucm_init_mode                    2
% 2.77/0.99  --bmc1_ucm_cone_mode                    none
% 2.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.99  --bmc1_ucm_relax_model                  4
% 2.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.99  --bmc1_ucm_layered_model                none
% 2.77/0.99  --bmc1_ucm_max_lemma_size               10
% 2.77/0.99  
% 2.77/0.99  ------ AIG Options
% 2.77/0.99  
% 2.77/0.99  --aig_mode                              false
% 2.77/0.99  
% 2.77/0.99  ------ Instantiation Options
% 2.77/0.99  
% 2.77/0.99  --instantiation_flag                    true
% 2.77/0.99  --inst_sos_flag                         false
% 2.77/0.99  --inst_sos_phase                        true
% 2.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.99  --inst_lit_sel_side                     num_symb
% 2.77/0.99  --inst_solver_per_active                1400
% 2.77/0.99  --inst_solver_calls_frac                1.
% 2.77/0.99  --inst_passive_queue_type               priority_queues
% 2.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.99  --inst_passive_queues_freq              [25;2]
% 2.77/0.99  --inst_dismatching                      true
% 2.77/0.99  --inst_eager_unprocessed_to_passive     true
% 2.77/0.99  --inst_prop_sim_given                   true
% 2.77/0.99  --inst_prop_sim_new                     false
% 2.77/0.99  --inst_subs_new                         false
% 2.77/0.99  --inst_eq_res_simp                      false
% 2.77/0.99  --inst_subs_given                       false
% 2.77/0.99  --inst_orphan_elimination               true
% 2.77/0.99  --inst_learning_loop_flag               true
% 2.77/0.99  --inst_learning_start                   3000
% 2.77/0.99  --inst_learning_factor                  2
% 2.77/0.99  --inst_start_prop_sim_after_learn       3
% 2.77/0.99  --inst_sel_renew                        solver
% 2.77/0.99  --inst_lit_activity_flag                true
% 2.77/0.99  --inst_restr_to_given                   false
% 2.77/0.99  --inst_activity_threshold               500
% 2.77/0.99  --inst_out_proof                        true
% 2.77/0.99  
% 2.77/0.99  ------ Resolution Options
% 2.77/0.99  
% 2.77/0.99  --resolution_flag                       true
% 2.77/0.99  --res_lit_sel                           adaptive
% 2.77/0.99  --res_lit_sel_side                      none
% 2.77/0.99  --res_ordering                          kbo
% 2.77/0.99  --res_to_prop_solver                    active
% 2.77/0.99  --res_prop_simpl_new                    false
% 2.77/0.99  --res_prop_simpl_given                  true
% 2.77/0.99  --res_passive_queue_type                priority_queues
% 2.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.99  --res_passive_queues_freq               [15;5]
% 2.77/0.99  --res_forward_subs                      full
% 2.77/0.99  --res_backward_subs                     full
% 2.77/0.99  --res_forward_subs_resolution           true
% 2.77/0.99  --res_backward_subs_resolution          true
% 2.77/0.99  --res_orphan_elimination                true
% 2.77/0.99  --res_time_limit                        2.
% 2.77/0.99  --res_out_proof                         true
% 2.77/0.99  
% 2.77/0.99  ------ Superposition Options
% 2.77/0.99  
% 2.77/0.99  --superposition_flag                    true
% 2.77/0.99  --sup_passive_queue_type                priority_queues
% 2.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.99  --demod_completeness_check              fast
% 2.77/0.99  --demod_use_ground                      true
% 2.77/0.99  --sup_to_prop_solver                    passive
% 2.77/0.99  --sup_prop_simpl_new                    true
% 2.77/0.99  --sup_prop_simpl_given                  true
% 2.77/0.99  --sup_fun_splitting                     false
% 2.77/0.99  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  ------ Parsing...
% 2.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.00  ------ Proving...
% 2.77/1.00  ------ Problem Properties 
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  clauses                                 33
% 2.77/1.00  conjectures                             2
% 2.77/1.00  EPR                                     12
% 2.77/1.00  Horn                                    23
% 2.77/1.00  unary                                   12
% 2.77/1.00  binary                                  7
% 2.77/1.00  lits                                    75
% 2.77/1.00  lits eq                                 26
% 2.77/1.00  fd_pure                                 0
% 2.77/1.00  fd_pseudo                               0
% 2.77/1.00  fd_cond                                 3
% 2.77/1.00  fd_pseudo_cond                          7
% 2.77/1.00  AC symbols                              0
% 2.77/1.00  
% 2.77/1.00  ------ Schedule dynamic 5 is on 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ 
% 2.77/1.00  Current options:
% 2.77/1.00  ------ 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options
% 2.77/1.00  
% 2.77/1.00  --out_options                           all
% 2.77/1.00  --tptp_safe_out                         true
% 2.77/1.00  --problem_path                          ""
% 2.77/1.00  --include_path                          ""
% 2.77/1.00  --clausifier                            res/vclausify_rel
% 2.77/1.00  --clausifier_options                    --mode clausify
% 2.77/1.00  --stdin                                 false
% 2.77/1.00  --stats_out                             all
% 2.77/1.00  
% 2.77/1.00  ------ General Options
% 2.77/1.00  
% 2.77/1.00  --fof                                   false
% 2.77/1.00  --time_out_real                         305.
% 2.77/1.00  --time_out_virtual                      -1.
% 2.77/1.00  --symbol_type_check                     false
% 2.77/1.00  --clausify_out                          false
% 2.77/1.00  --sig_cnt_out                           false
% 2.77/1.00  --trig_cnt_out                          false
% 2.77/1.00  --trig_cnt_out_tolerance                1.
% 2.77/1.00  --trig_cnt_out_sk_spl                   false
% 2.77/1.00  --abstr_cl_out                          false
% 2.77/1.00  
% 2.77/1.00  ------ Global Options
% 2.77/1.00  
% 2.77/1.00  --schedule                              default
% 2.77/1.00  --add_important_lit                     false
% 2.77/1.00  --prop_solver_per_cl                    1000
% 2.77/1.00  --min_unsat_core                        false
% 2.77/1.00  --soft_assumptions                      false
% 2.77/1.00  --soft_lemma_size                       3
% 2.77/1.00  --prop_impl_unit_size                   0
% 2.77/1.00  --prop_impl_unit                        []
% 2.77/1.00  --share_sel_clauses                     true
% 2.77/1.00  --reset_solvers                         false
% 2.77/1.00  --bc_imp_inh                            [conj_cone]
% 2.77/1.00  --conj_cone_tolerance                   3.
% 2.77/1.00  --extra_neg_conj                        none
% 2.77/1.00  --large_theory_mode                     true
% 2.77/1.00  --prolific_symb_bound                   200
% 2.77/1.00  --lt_threshold                          2000
% 2.77/1.00  --clause_weak_htbl                      true
% 2.77/1.00  --gc_record_bc_elim                     false
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing Options
% 2.77/1.00  
% 2.77/1.00  --preprocessing_flag                    true
% 2.77/1.00  --time_out_prep_mult                    0.1
% 2.77/1.00  --splitting_mode                        input
% 2.77/1.00  --splitting_grd                         true
% 2.77/1.00  --splitting_cvd                         false
% 2.77/1.00  --splitting_cvd_svl                     false
% 2.77/1.00  --splitting_nvd                         32
% 2.77/1.00  --sub_typing                            true
% 2.77/1.00  --prep_gs_sim                           true
% 2.77/1.00  --prep_unflatten                        true
% 2.77/1.00  --prep_res_sim                          true
% 2.77/1.00  --prep_upred                            true
% 2.77/1.00  --prep_sem_filter                       exhaustive
% 2.77/1.00  --prep_sem_filter_out                   false
% 2.77/1.00  --pred_elim                             true
% 2.77/1.00  --res_sim_input                         true
% 2.77/1.00  --eq_ax_congr_red                       true
% 2.77/1.00  --pure_diseq_elim                       true
% 2.77/1.00  --brand_transform                       false
% 2.77/1.00  --non_eq_to_eq                          false
% 2.77/1.00  --prep_def_merge                        true
% 2.77/1.00  --prep_def_merge_prop_impl              false
% 2.77/1.00  --prep_def_merge_mbd                    true
% 2.77/1.00  --prep_def_merge_tr_red                 false
% 2.77/1.00  --prep_def_merge_tr_cl                  false
% 2.77/1.00  --smt_preprocessing                     true
% 2.77/1.00  --smt_ac_axioms                         fast
% 2.77/1.00  --preprocessed_out                      false
% 2.77/1.00  --preprocessed_stats                    false
% 2.77/1.00  
% 2.77/1.00  ------ Abstraction refinement Options
% 2.77/1.00  
% 2.77/1.00  --abstr_ref                             []
% 2.77/1.00  --abstr_ref_prep                        false
% 2.77/1.00  --abstr_ref_until_sat                   false
% 2.77/1.00  --abstr_ref_sig_restrict                funpre
% 2.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.00  --abstr_ref_under                       []
% 2.77/1.00  
% 2.77/1.00  ------ SAT Options
% 2.77/1.00  
% 2.77/1.00  --sat_mode                              false
% 2.77/1.00  --sat_fm_restart_options                ""
% 2.77/1.00  --sat_gr_def                            false
% 2.77/1.00  --sat_epr_types                         true
% 2.77/1.00  --sat_non_cyclic_types                  false
% 2.77/1.00  --sat_finite_models                     false
% 2.77/1.00  --sat_fm_lemmas                         false
% 2.77/1.00  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     none
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       false
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ Proving...
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS status Theorem for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  fof(f14,conjecture,(
% 2.77/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f15,negated_conjecture,(
% 2.77/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.77/1.00    inference(negated_conjecture,[],[f14])).
% 2.77/1.00  
% 2.77/1.00  fof(f20,plain,(
% 2.77/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.77/1.00    inference(ennf_transformation,[],[f15])).
% 2.77/1.00  
% 2.77/1.00  fof(f21,plain,(
% 2.77/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.77/1.00    inference(flattening,[],[f20])).
% 2.77/1.00  
% 2.77/1.00  fof(f45,plain,(
% 2.77/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f46,plain,(
% 2.77/1.00    k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9)),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f45])).
% 2.77/1.00  
% 2.77/1.00  fof(f86,plain,(
% 2.77/1.00    v1_funct_2(sK9,sK6,k1_tarski(sK7))),
% 2.77/1.00    inference(cnf_transformation,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f3,axiom,(
% 2.77/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f57,plain,(
% 2.77/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f3])).
% 2.77/1.00  
% 2.77/1.00  fof(f4,axiom,(
% 2.77/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f58,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f4])).
% 2.77/1.00  
% 2.77/1.00  fof(f5,axiom,(
% 2.77/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f59,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f5])).
% 2.77/1.00  
% 2.77/1.00  fof(f6,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f60,plain,(
% 2.77/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f6])).
% 2.77/1.00  
% 2.77/1.00  fof(f7,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f61,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f7])).
% 2.77/1.00  
% 2.77/1.00  fof(f8,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f62,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f8])).
% 2.77/1.00  
% 2.77/1.00  fof(f9,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f63,plain,(
% 2.77/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f9])).
% 2.77/1.00  
% 2.77/1.00  fof(f90,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f62,f63])).
% 2.77/1.00  
% 2.77/1.00  fof(f91,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f61,f90])).
% 2.77/1.00  
% 2.77/1.00  fof(f92,plain,(
% 2.77/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f60,f91])).
% 2.77/1.00  
% 2.77/1.00  fof(f93,plain,(
% 2.77/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f59,f92])).
% 2.77/1.00  
% 2.77/1.00  fof(f94,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f58,f93])).
% 2.77/1.00  
% 2.77/1.00  fof(f95,plain,(
% 2.77/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.77/1.00    inference(definition_unfolding,[],[f57,f94])).
% 2.77/1.00  
% 2.77/1.00  fof(f103,plain,(
% 2.77/1.00    v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))),
% 2.77/1.00    inference(definition_unfolding,[],[f86,f95])).
% 2.77/1.00  
% 2.77/1.00  fof(f13,axiom,(
% 2.77/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f18,plain,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.77/1.00    inference(ennf_transformation,[],[f13])).
% 2.77/1.00  
% 2.77/1.00  fof(f19,plain,(
% 2.77/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.77/1.00    inference(flattening,[],[f18])).
% 2.77/1.00  
% 2.77/1.00  fof(f84,plain,(
% 2.77/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f19])).
% 2.77/1.00  
% 2.77/1.00  fof(f87,plain,(
% 2.77/1.00    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 2.77/1.00    inference(cnf_transformation,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f102,plain,(
% 2.77/1.00    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))))),
% 2.77/1.00    inference(definition_unfolding,[],[f87,f95])).
% 2.77/1.00  
% 2.77/1.00  fof(f85,plain,(
% 2.77/1.00    v1_funct_1(sK9)),
% 2.77/1.00    inference(cnf_transformation,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f88,plain,(
% 2.77/1.00    r2_hidden(sK8,sK6)),
% 2.77/1.00    inference(cnf_transformation,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f89,plain,(
% 2.77/1.00    k1_funct_1(sK9,sK8) != sK7),
% 2.77/1.00    inference(cnf_transformation,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f2,axiom,(
% 2.77/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f30,plain,(
% 2.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.77/1.00    inference(nnf_transformation,[],[f2])).
% 2.77/1.00  
% 2.77/1.00  fof(f31,plain,(
% 2.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.77/1.00    inference(rectify,[],[f30])).
% 2.77/1.00  
% 2.77/1.00  fof(f32,plain,(
% 2.77/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f33,plain,(
% 2.77/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.77/1.00  
% 2.77/1.00  fof(f53,plain,(
% 2.77/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.77/1.00    inference(cnf_transformation,[],[f33])).
% 2.77/1.00  
% 2.77/1.00  fof(f99,plain,(
% 2.77/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.77/1.00    inference(definition_unfolding,[],[f53,f95])).
% 2.77/1.00  
% 2.77/1.00  fof(f109,plain,(
% 2.77/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.77/1.00    inference(equality_resolution,[],[f99])).
% 2.77/1.00  
% 2.77/1.00  fof(f54,plain,(
% 2.77/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.77/1.00    inference(cnf_transformation,[],[f33])).
% 2.77/1.00  
% 2.77/1.00  fof(f98,plain,(
% 2.77/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.77/1.00    inference(definition_unfolding,[],[f54,f95])).
% 2.77/1.00  
% 2.77/1.00  fof(f107,plain,(
% 2.77/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 2.77/1.00    inference(equality_resolution,[],[f98])).
% 2.77/1.00  
% 2.77/1.00  fof(f108,plain,(
% 2.77/1.00    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 2.77/1.00    inference(equality_resolution,[],[f107])).
% 2.77/1.00  
% 2.77/1.00  fof(f12,axiom,(
% 2.77/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f17,plain,(
% 2.77/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.77/1.00    inference(ennf_transformation,[],[f12])).
% 2.77/1.00  
% 2.77/1.00  fof(f43,plain,(
% 2.77/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f44,plain,(
% 2.77/1.00    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f43])).
% 2.77/1.00  
% 2.77/1.00  fof(f81,plain,(
% 2.77/1.00    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 2.77/1.00    inference(cnf_transformation,[],[f44])).
% 2.77/1.00  
% 2.77/1.00  fof(f1,axiom,(
% 2.77/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f25,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/1.00    inference(nnf_transformation,[],[f1])).
% 2.77/1.00  
% 2.77/1.00  fof(f26,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/1.00    inference(flattening,[],[f25])).
% 2.77/1.00  
% 2.77/1.00  fof(f27,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/1.00    inference(rectify,[],[f26])).
% 2.77/1.00  
% 2.77/1.00  fof(f28,plain,(
% 2.77/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f29,plain,(
% 2.77/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 2.77/1.00  
% 2.77/1.00  fof(f47,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.77/1.00    inference(cnf_transformation,[],[f29])).
% 2.77/1.00  
% 2.77/1.00  fof(f106,plain,(
% 2.77/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.77/1.00    inference(equality_resolution,[],[f47])).
% 2.77/1.00  
% 2.77/1.00  fof(f48,plain,(
% 2.77/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.77/1.00    inference(cnf_transformation,[],[f29])).
% 2.77/1.00  
% 2.77/1.00  fof(f105,plain,(
% 2.77/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.77/1.00    inference(equality_resolution,[],[f48])).
% 2.77/1.00  
% 2.77/1.00  cnf(c_34,negated_conjecture,
% 2.77/1.00      ( v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_30,plain,
% 2.77/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.00      | ~ r2_hidden(X3,X1)
% 2.77/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.77/1.00      | ~ v1_funct_1(X0)
% 2.77/1.00      | k1_xboole_0 = X2 ),
% 2.77/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_33,negated_conjecture,
% 2.77/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
% 2.77/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_449,plain,
% 2.77/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.00      | ~ r2_hidden(X3,X1)
% 2.77/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.77/1.00      | ~ v1_funct_1(X0)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.77/1.00      | sK9 != X0
% 2.77/1.00      | k1_xboole_0 = X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_33]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_450,plain,
% 2.77/1.00      ( ~ v1_funct_2(sK9,X0,X1)
% 2.77/1.00      | ~ r2_hidden(X2,X0)
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X2),X1)
% 2.77/1.00      | ~ v1_funct_1(sK9)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.00      | k1_xboole_0 = X1 ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_35,negated_conjecture,
% 2.77/1.00      ( v1_funct_1(sK9) ),
% 2.77/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_454,plain,
% 2.77/1.00      ( r2_hidden(k1_funct_1(sK9,X2),X1)
% 2.77/1.00      | ~ r2_hidden(X2,X0)
% 2.77/1.00      | ~ v1_funct_2(sK9,X0,X1)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.00      | k1_xboole_0 = X1 ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_450,c_35]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_455,plain,
% 2.77/1.00      ( ~ v1_funct_2(sK9,X0,X1)
% 2.77/1.00      | ~ r2_hidden(X2,X0)
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X2),X1)
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.00      | k1_xboole_0 = X1 ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_454]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_482,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,X1)
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X0),X2)
% 2.77/1.00      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X2
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.77/1.00      | sK6 != X1
% 2.77/1.00      | sK9 != sK9
% 2.77/1.00      | k1_xboole_0 = X2 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_34,c_455]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_483,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,sK6)
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 2.77/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))
% 2.77/1.00      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1076,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,sK6)
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 2.77/1.00      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 2.77/1.00      inference(equality_resolution_simp,[status(thm)],[c_483]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2541,plain,
% 2.77/1.00      ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
% 2.77/1.00      | r2_hidden(X0,sK6) != iProver_top
% 2.77/1.00      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_32,negated_conjecture,
% 2.77/1.00      ( r2_hidden(sK8,sK6) ),
% 2.77/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_31,negated_conjecture,
% 2.77/1.00      ( k1_funct_1(sK9,sK8) != sK7 ),
% 2.77/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2790,plain,
% 2.77/1.00      ( r2_hidden(k1_funct_1(sK9,sK8),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 2.77/1.00      | ~ r2_hidden(sK8,sK6)
% 2.77/1.00      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1076]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_9,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.77/1.00      inference(cnf_transformation,[],[f109]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2827,plain,
% 2.77/1.00      ( ~ r2_hidden(k1_funct_1(sK9,sK8),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 2.77/1.00      | k1_funct_1(sK9,sK8) = sK7 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2857,plain,
% 2.77/1.00      ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_2541,c_32,c_31,c_2790,c_2827]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_8,plain,
% 2.77/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f108]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2564,plain,
% 2.77/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3121,plain,
% 2.77/1.00      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2857,c_2564]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_29,plain,
% 2.77/1.00      ( r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2543,plain,
% 2.77/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5,plain,
% 2.77/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2567,plain,
% 2.77/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.77/1.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3261,plain,
% 2.77/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.77/1.00      | r2_hidden(sK5(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2543,c_2567]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2563,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3405,plain,
% 2.77/1.00      ( sK7 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2857,c_2563]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_10651,plain,
% 2.77/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0
% 2.77/1.00      | sK5(k4_xboole_0(k1_xboole_0,X0)) = sK7 ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3261,c_3405]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2568,plain,
% 2.77/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.77/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3268,plain,
% 2.77/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.77/1.00      | r2_hidden(sK5(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2543,c_2568]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_11604,plain,
% 2.77/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0
% 2.77/1.00      | r2_hidden(sK7,X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_10651,c_3268]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_12389,plain,
% 2.77/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3121,c_11604]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_12420,plain,
% 2.77/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_12389,c_2568]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_12676,plain,
% 2.77/1.00      ( r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_12420]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(contradiction,plain,
% 2.77/1.00      ( $false ),
% 2.77/1.00      inference(minisat,[status(thm)],[c_12676,c_3121]) ).
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  ------                               Statistics
% 2.77/1.00  
% 2.77/1.00  ------ General
% 2.77/1.00  
% 2.77/1.00  abstr_ref_over_cycles:                  0
% 2.77/1.00  abstr_ref_under_cycles:                 0
% 2.77/1.00  gc_basic_clause_elim:                   0
% 2.77/1.00  forced_gc_time:                         0
% 2.77/1.00  parsing_time:                           0.01
% 2.77/1.00  unif_index_cands_time:                  0.
% 2.77/1.00  unif_index_add_time:                    0.
% 2.77/1.00  orderings_time:                         0.
% 2.77/1.00  out_proof_time:                         0.015
% 2.77/1.00  total_time:                             0.4
% 2.77/1.00  num_of_symbols:                         52
% 2.77/1.00  num_of_terms:                           16101
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing
% 2.77/1.00  
% 2.77/1.00  num_of_splits:                          0
% 2.77/1.00  num_of_split_atoms:                     0
% 2.77/1.00  num_of_reused_defs:                     0
% 2.77/1.00  num_eq_ax_congr_red:                    108
% 2.77/1.00  num_of_sem_filtered_clauses:            1
% 2.77/1.00  num_of_subtypes:                        0
% 2.77/1.00  monotx_restored_types:                  0
% 2.77/1.00  sat_num_of_epr_types:                   0
% 2.77/1.00  sat_num_of_non_cyclic_types:            0
% 2.77/1.00  sat_guarded_non_collapsed_types:        0
% 2.77/1.00  num_pure_diseq_elim:                    0
% 2.77/1.00  simp_replaced_by:                       0
% 2.77/1.00  res_preprocessed:                       152
% 2.77/1.00  prep_upred:                             0
% 2.77/1.00  prep_unflattend:                        599
% 2.77/1.00  smt_new_axioms:                         0
% 2.77/1.00  pred_elim_cands:                        3
% 2.77/1.00  pred_elim:                              3
% 2.77/1.00  pred_elim_cl:                           3
% 2.77/1.00  pred_elim_cycles:                       7
% 2.77/1.00  merged_defs:                            8
% 2.77/1.00  merged_defs_ncl:                        0
% 2.77/1.00  bin_hyper_res:                          8
% 2.77/1.00  prep_cycles:                            4
% 2.77/1.00  pred_elim_time:                         0.031
% 2.77/1.00  splitting_time:                         0.
% 2.77/1.00  sem_filter_time:                        0.
% 2.77/1.00  monotx_time:                            0.001
% 2.77/1.00  subtype_inf_time:                       0.
% 2.77/1.00  
% 2.77/1.00  ------ Problem properties
% 2.77/1.00  
% 2.77/1.00  clauses:                                33
% 2.77/1.00  conjectures:                            2
% 2.77/1.00  epr:                                    12
% 2.77/1.00  horn:                                   23
% 2.77/1.00  ground:                                 2
% 2.77/1.00  unary:                                  12
% 2.77/1.00  binary:                                 7
% 2.77/1.00  lits:                                   75
% 2.77/1.00  lits_eq:                                26
% 2.77/1.00  fd_pure:                                0
% 2.77/1.00  fd_pseudo:                              0
% 2.77/1.00  fd_cond:                                3
% 2.77/1.00  fd_pseudo_cond:                         7
% 2.77/1.00  ac_symbols:                             0
% 2.77/1.00  
% 2.77/1.00  ------ Propositional Solver
% 2.77/1.00  
% 2.77/1.00  prop_solver_calls:                      28
% 2.77/1.00  prop_fast_solver_calls:                 1105
% 2.77/1.00  smt_solver_calls:                       0
% 2.77/1.00  smt_fast_solver_calls:                  0
% 2.77/1.00  prop_num_of_clauses:                    3845
% 2.77/1.00  prop_preprocess_simplified:             13377
% 2.77/1.00  prop_fo_subsumed:                       4
% 2.77/1.00  prop_solver_time:                       0.
% 2.77/1.00  smt_solver_time:                        0.
% 2.77/1.00  smt_fast_solver_time:                   0.
% 2.77/1.00  prop_fast_solver_time:                  0.
% 2.77/1.00  prop_unsat_core_time:                   0.
% 2.77/1.00  
% 2.77/1.00  ------ QBF
% 2.77/1.00  
% 2.77/1.00  qbf_q_res:                              0
% 2.77/1.00  qbf_num_tautologies:                    0
% 2.77/1.00  qbf_prep_cycles:                        0
% 2.77/1.00  
% 2.77/1.00  ------ BMC1
% 2.77/1.00  
% 2.77/1.00  bmc1_current_bound:                     -1
% 2.77/1.00  bmc1_last_solved_bound:                 -1
% 2.77/1.00  bmc1_unsat_core_size:                   -1
% 2.77/1.00  bmc1_unsat_core_parents_size:           -1
% 2.77/1.00  bmc1_merge_next_fun:                    0
% 2.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation
% 2.77/1.00  
% 2.77/1.00  inst_num_of_clauses:                    1262
% 2.77/1.00  inst_num_in_passive:                    409
% 2.77/1.00  inst_num_in_active:                     300
% 2.77/1.00  inst_num_in_unprocessed:                553
% 2.77/1.00  inst_num_of_loops:                      350
% 2.77/1.00  inst_num_of_learning_restarts:          0
% 2.77/1.00  inst_num_moves_active_passive:          49
% 2.77/1.00  inst_lit_activity:                      0
% 2.77/1.00  inst_lit_activity_moves:                0
% 2.77/1.00  inst_num_tautologies:                   0
% 2.77/1.00  inst_num_prop_implied:                  0
% 2.77/1.00  inst_num_existing_simplified:           0
% 2.77/1.00  inst_num_eq_res_simplified:             0
% 2.77/1.00  inst_num_child_elim:                    0
% 2.77/1.00  inst_num_of_dismatching_blockings:      652
% 2.77/1.00  inst_num_of_non_proper_insts:           1126
% 2.77/1.00  inst_num_of_duplicates:                 0
% 2.77/1.00  inst_inst_num_from_inst_to_res:         0
% 2.77/1.00  inst_dismatching_checking_time:         0.
% 2.77/1.00  
% 2.77/1.00  ------ Resolution
% 2.77/1.00  
% 2.77/1.00  res_num_of_clauses:                     0
% 2.77/1.00  res_num_in_passive:                     0
% 2.77/1.00  res_num_in_active:                      0
% 2.77/1.00  res_num_of_loops:                       156
% 2.77/1.00  res_forward_subset_subsumed:            267
% 2.77/1.00  res_backward_subset_subsumed:           0
% 2.77/1.00  res_forward_subsumed:                   0
% 2.77/1.00  res_backward_subsumed:                  0
% 2.77/1.00  res_forward_subsumption_resolution:     0
% 2.77/1.00  res_backward_subsumption_resolution:    0
% 2.77/1.00  res_clause_to_clause_subsumption:       1522
% 2.77/1.00  res_orphan_elimination:                 0
% 2.77/1.00  res_tautology_del:                      61
% 2.77/1.00  res_num_eq_res_simplified:              1
% 2.77/1.00  res_num_sel_changes:                    0
% 2.77/1.00  res_moves_from_active_to_pass:          0
% 2.77/1.00  
% 2.77/1.00  ------ Superposition
% 2.77/1.00  
% 2.77/1.00  sup_time_total:                         0.
% 2.77/1.00  sup_time_generating:                    0.
% 2.77/1.00  sup_time_sim_full:                      0.
% 2.77/1.00  sup_time_sim_immed:                     0.
% 2.77/1.00  
% 2.77/1.00  sup_num_of_clauses:                     176
% 2.77/1.00  sup_num_in_active:                      65
% 2.77/1.00  sup_num_in_passive:                     111
% 2.77/1.00  sup_num_of_loops:                       68
% 2.77/1.00  sup_fw_superposition:                   107
% 2.77/1.00  sup_bw_superposition:                   149
% 2.77/1.00  sup_immediate_simplified:               46
% 2.77/1.00  sup_given_eliminated:                   1
% 2.77/1.00  comparisons_done:                       0
% 2.77/1.00  comparisons_avoided:                    30
% 2.77/1.00  
% 2.77/1.00  ------ Simplifications
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  sim_fw_subset_subsumed:                 25
% 2.77/1.00  sim_bw_subset_subsumed:                 8
% 2.77/1.00  sim_fw_subsumed:                        21
% 2.77/1.00  sim_bw_subsumed:                        10
% 2.77/1.00  sim_fw_subsumption_res:                 7
% 2.77/1.00  sim_bw_subsumption_res:                 0
% 2.77/1.00  sim_tautology_del:                      16
% 2.77/1.00  sim_eq_tautology_del:                   12
% 2.77/1.00  sim_eq_res_simp:                        1
% 2.77/1.00  sim_fw_demodulated:                     0
% 2.77/1.00  sim_bw_demodulated:                     0
% 2.77/1.00  sim_light_normalised:                   12
% 2.77/1.00  sim_joinable_taut:                      0
% 2.77/1.00  sim_joinable_simp:                      0
% 2.77/1.00  sim_ac_normalised:                      0
% 2.77/1.00  sim_smt_subsumption:                    0
% 2.77/1.00  
%------------------------------------------------------------------------------
