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
% DateTime   : Thu Dec  3 11:58:33 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  173 (3321 expanded)
%              Number of clauses        :   86 ( 877 expanded)
%              Number of leaves         :   22 ( 982 expanded)
%              Depth                    :   21
%              Number of atoms          :  593 (14884 expanded)
%              Number of equality atoms :  464 (11635 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f106,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f62,f63])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK6) = sK6
          | k6_mcart_1(X0,X1,X2,sK6) = sK6
          | k5_mcart_1(X0,X1,X2,sK6) = sK6 )
        & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK3,sK4,sK5,X3) = X3
            | k6_mcart_1(sK3,sK4,sK5,X3) = X3
            | k5_mcart_1(sK3,sK4,sK5,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f39,f38])).

fof(f78,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f78,f63])).

fof(f75,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f83])).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f104])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f63])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f63])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f62])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f98,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f97])).

fof(f79,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f65])).

fof(f74,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f62])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f102,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f101])).

cnf(c_23,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1128,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1136,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2602,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1128,c_1136])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1131,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3015,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1131])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1407,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1409,plain,
    ( k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_1,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1408,plain,
    ( k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3366,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3015,c_1409,c_1408])).

cnf(c_3759,plain,
    ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2602,c_3366])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_407,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_408,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1488,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_408])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_73,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_76,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_645,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1401,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1402,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1403,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1404,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1405,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1406,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1755,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_389,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_390,plain,
    ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1452,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_390])).

cnf(c_1608,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_353,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_354,plain,
    ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1458,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_354])).

cnf(c_1654,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1458,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_371,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_372,plain,
    ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1482,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_372])).

cnf(c_1749,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1482,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406])).

cnf(c_1757,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_1755,c_1608,c_1654,c_1749])).

cnf(c_29,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1759,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_1757,c_29])).

cnf(c_1884,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_1759,c_1757])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1130,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2525,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1130])).

cnf(c_2758,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_2525])).

cnf(c_3765,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3759,c_2758])).

cnf(c_4161,plain,
    ( sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3765,c_3366])).

cnf(c_4165,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4161])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1143,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1611,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_30,c_1608])).

cnf(c_1752,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_1611,c_1749])).

cnf(c_1754,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_1752,c_1654])).

cnf(c_1885,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_1754,c_1759])).

cnf(c_19,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_28,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1173,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_19,c_28])).

cnf(c_1996,plain,
    ( k2_mcart_1(sK6) != sK6 ),
    inference(superposition,[status(thm)],[c_1884,c_1173])).

cnf(c_2059,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_1996])).

cnf(c_2060,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_2059])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1129,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1942,plain,
    ( k4_tarski(sK6,X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1129])).

cnf(c_3773,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k4_tarski(sK6,X1) != X0
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3759,c_1942])).

cnf(c_4339,plain,
    ( k4_tarski(sK6,X0) != X1
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3773,c_3366])).

cnf(c_4343,plain,
    ( k1_mcart_1(sK6) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_4339])).

cnf(c_5013,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4343,c_1136])).

cnf(c_5017,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_1143,c_5013])).

cnf(c_5558,plain,
    ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4165,c_5017])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1141,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5560,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5558,c_1141])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.20/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.99  
% 3.20/0.99  ------  iProver source info
% 3.20/0.99  
% 3.20/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.99  git: non_committed_changes: false
% 3.20/0.99  git: last_make_outside_of_git: false
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     num_symb
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       true
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 34
% 3.20/0.99  conjectures                             4
% 3.20/0.99  EPR                                     3
% 3.20/0.99  Horn                                    24
% 3.20/0.99  unary                                   13
% 3.20/0.99  binary                                  6
% 3.20/0.99  lits                                    81
% 3.20/0.99  lits eq                                 60
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 7
% 3.20/0.99  fd_pseudo_cond                          6
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Schedule dynamic 5 is on 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     none
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       false
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99   Resolution empty clause
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f12,axiom,(
% 3.20/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f20,plain,(
% 3.20/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.20/0.99    inference(ennf_transformation,[],[f12])).
% 3.20/0.99  
% 3.20/0.99  fof(f36,plain,(
% 3.20/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f37,plain,(
% 3.20/0.99    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).
% 3.20/0.99  
% 3.20/0.99  fof(f66,plain,(
% 3.20/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f4,axiom,(
% 3.20/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.20/0.99    inference(nnf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.20/0.99    inference(rectify,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f31,plain,(
% 3.20/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f32,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f51,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.20/0.99    inference(cnf_transformation,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f5,axiom,(
% 3.20/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f55,plain,(
% 3.20/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f5])).
% 3.20/0.99  
% 3.20/0.99  fof(f6,axiom,(
% 3.20/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f56,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f6])).
% 3.20/0.99  
% 3.20/0.99  fof(f80,plain,(
% 3.20/0.99    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f55,f56])).
% 3.20/0.99  
% 3.20/0.99  fof(f84,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.20/0.99    inference(definition_unfolding,[],[f51,f80])).
% 3.20/0.99  
% 3.20/0.99  fof(f106,plain,(
% 3.20/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.20/0.99    inference(equality_resolution,[],[f84])).
% 3.20/0.99  
% 3.20/0.99  fof(f1,axiom,(
% 3.20/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f41,plain,(
% 3.20/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f1])).
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f34,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.20/0.99    inference(nnf_transformation,[],[f8])).
% 3.20/0.99  
% 3.20/0.99  fof(f35,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.20/0.99    inference(flattening,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f59,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f35])).
% 3.20/0.99  
% 3.20/0.99  fof(f89,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f59,f56])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f33,plain,(
% 3.20/0.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.20/0.99    inference(nnf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f57,plain,(
% 3.20/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f33])).
% 3.20/0.99  
% 3.20/0.99  fof(f86,plain,(
% 3.20/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f57,f80])).
% 3.20/0.99  
% 3.20/0.99  fof(f2,axiom,(
% 3.20/0.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f42,plain,(
% 3.20/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f2])).
% 3.20/0.99  
% 3.20/0.99  fof(f13,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f21,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.20/0.99    inference(ennf_transformation,[],[f13])).
% 3.20/0.99  
% 3.20/0.99  fof(f69,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f21])).
% 3.20/0.99  
% 3.20/0.99  fof(f9,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f62,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f9])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f63,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f92,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f69,f62,f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f16,conjecture,(
% 3.20/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f17,negated_conjecture,(
% 3.20/0.99    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.20/0.99    inference(negated_conjecture,[],[f16])).
% 3.20/0.99  
% 3.20/0.99  fof(f23,plain,(
% 3.20/0.99    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.20/0.99    inference(ennf_transformation,[],[f17])).
% 3.20/0.99  
% 3.20/0.99  fof(f39,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f38,plain,(
% 3.20/0.99    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f40,plain,(
% 3.20/0.99    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f39,f38])).
% 3.20/0.99  
% 3.20/0.99  fof(f78,plain,(
% 3.20/0.99    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.20/0.99    inference(cnf_transformation,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f96,plain,(
% 3.20/0.99    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 3.20/0.99    inference(definition_unfolding,[],[f78,f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f75,plain,(
% 3.20/0.99    k1_xboole_0 != sK3),
% 3.20/0.99    inference(cnf_transformation,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f76,plain,(
% 3.20/0.99    k1_xboole_0 != sK4),
% 3.20/0.99    inference(cnf_transformation,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f77,plain,(
% 3.20/0.99    k1_xboole_0 != sK5),
% 3.20/0.99    inference(cnf_transformation,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f52,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.20/0.99    inference(cnf_transformation,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f83,plain,(
% 3.20/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.20/0.99    inference(definition_unfolding,[],[f52,f80])).
% 3.20/0.99  
% 3.20/0.99  fof(f104,plain,(
% 3.20/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.20/0.99    inference(equality_resolution,[],[f83])).
% 3.20/0.99  
% 3.20/0.99  fof(f105,plain,(
% 3.20/0.99    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.20/0.99    inference(equality_resolution,[],[f104])).
% 3.20/0.99  
% 3.20/0.99  fof(f14,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f22,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.20/0.99    inference(ennf_transformation,[],[f14])).
% 3.20/0.99  
% 3.20/0.99  fof(f72,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f93,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f72,f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f70,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f95,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f70,f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f71,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f94,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f71,f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f15,axiom,(
% 3.20/0.99    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f73,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f68,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f90,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f68,f62])).
% 3.20/0.99  
% 3.20/0.99  fof(f3,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f18,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.20/0.99    inference(ennf_transformation,[],[f3])).
% 3.20/0.99  
% 3.20/0.99  fof(f24,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.99    inference(nnf_transformation,[],[f18])).
% 3.20/0.99  
% 3.20/0.99  fof(f25,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.99    inference(flattening,[],[f24])).
% 3.20/0.99  
% 3.20/0.99  fof(f26,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.99    inference(rectify,[],[f25])).
% 3.20/0.99  
% 3.20/0.99  fof(f27,plain,(
% 3.20/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f28,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.20/0.99  
% 3.20/0.99  fof(f46,plain,(
% 3.20/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f97,plain,(
% 3.20/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.20/0.99    inference(equality_resolution,[],[f46])).
% 3.20/0.99  
% 3.20/0.99  fof(f98,plain,(
% 3.20/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.20/0.99    inference(equality_resolution,[],[f97])).
% 3.20/0.99  
% 3.20/0.99  fof(f79,plain,(
% 3.20/0.99    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 3.20/0.99    inference(cnf_transformation,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f11,axiom,(
% 3.20/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f19,plain,(
% 3.20/0.99    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.20/0.99    inference(ennf_transformation,[],[f11])).
% 3.20/0.99  
% 3.20/0.99  fof(f65,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f19])).
% 3.20/0.99  
% 3.20/0.99  fof(f107,plain,(
% 3.20/0.99    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 3.20/0.99    inference(equality_resolution,[],[f65])).
% 3.20/0.99  
% 3.20/0.99  fof(f74,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.20/0.99    inference(cnf_transformation,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f67,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(cnf_transformation,[],[f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f91,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.20/0.99    inference(definition_unfolding,[],[f67,f62])).
% 3.20/0.99  
% 3.20/0.99  fof(f44,plain,(
% 3.20/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f101,plain,(
% 3.20/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.20/0.99    inference(equality_resolution,[],[f44])).
% 3.20/0.99  
% 3.20/0.99  fof(f102,plain,(
% 3.20/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.20/0.99    inference(equality_resolution,[],[f101])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_23,plain,
% 3.20/0.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1128,plain,
% 3.20/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1136,plain,
% 3.20/0.99      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2602,plain,
% 3.20/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0 | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1128,c_1136]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_0,plain,
% 3.20/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_18,plain,
% 3.20/0.99      ( r2_hidden(X0,X1)
% 3.20/0.99      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1131,plain,
% 3.20/0.99      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
% 3.20/0.99      | r2_hidden(X0,X2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3015,plain,
% 3.20/0.99      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 3.20/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_0,c_1131]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_15,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) != X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1407,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,k1_xboole_0)
% 3.20/0.99      | k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) != k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1409,plain,
% 3.20/0.99      ( k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) != k1_xboole_0
% 3.20/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1408,plain,
% 3.20/0.99      ( k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) = k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3366,plain,
% 3.20/0.99      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3015,c_1409,c_1408]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3759,plain,
% 3.20/0.99      ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2602,c_3366]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_24,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.20/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2
% 3.20/0.99      | k1_xboole_0 = X3 ),
% 3.20/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_31,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_407,plain,
% 3.20/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 3.20/0.99      | sK6 != X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_408,plain,
% 3.20/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1488,plain,
% 3.20/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 3.20/0.99      | sK5 = k1_xboole_0
% 3.20/0.99      | sK4 = k1_xboole_0
% 3.20/0.99      | sK3 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_408]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_34,negated_conjecture,
% 3.20/0.99      ( k1_xboole_0 != sK3 ),
% 3.20/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_33,negated_conjecture,
% 3.20/0.99      ( k1_xboole_0 != sK4 ),
% 3.20/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_32,negated_conjecture,
% 3.20/0.99      ( k1_xboole_0 != sK5 ),
% 3.20/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_73,plain,
% 3.20/0.99      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.20/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,plain,
% 3.20/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_76,plain,
% 3.20/0.99      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_645,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1401,plain,
% 3.20/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_645]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1402,plain,
% 3.20/0.99      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1403,plain,
% 3.20/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_645]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1404,plain,
% 3.20/0.99      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1403]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1405,plain,
% 3.20/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_645]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1406,plain,
% 3.20/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1405]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1755,plain,
% 3.20/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1488,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_25,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.20/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2
% 3.20/0.99      | k1_xboole_0 = X3 ),
% 3.20/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_389,plain,
% 3.20/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | sK6 != X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_390,plain,
% 3.20/0.99      ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1452,plain,
% 3.20/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 3.20/0.99      | sK5 = k1_xboole_0
% 3.20/0.99      | sK4 = k1_xboole_0
% 3.20/0.99      | sK3 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_390]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1608,plain,
% 3.20/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1452,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_27,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.20/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2
% 3.20/0.99      | k1_xboole_0 = X3 ),
% 3.20/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_353,plain,
% 3.20/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | sK6 != X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_354,plain,
% 3.20/0.99      ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1458,plain,
% 3.20/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 3.20/0.99      | sK5 = k1_xboole_0
% 3.20/0.99      | sK4 = k1_xboole_0
% 3.20/0.99      | sK3 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_354]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1654,plain,
% 3.20/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1458,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_26,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.20/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2
% 3.20/0.99      | k1_xboole_0 = X3 ),
% 3.20/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_371,plain,
% 3.20/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | sK6 != X3
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_372,plain,
% 3.20/0.99      ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 3.20/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1482,plain,
% 3.20/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 3.20/0.99      | sK5 = k1_xboole_0
% 3.20/0.99      | sK4 = k1_xboole_0
% 3.20/0.99      | sK3 = k1_xboole_0 ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_372]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1749,plain,
% 3.20/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1482,c_34,c_33,c_32,c_73,c_76,c_1402,c_1404,c_1406]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1757,plain,
% 3.20/0.99      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 3.20/0.99      inference(light_normalisation,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1755,c_1608,c_1654,c_1749]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_29,plain,
% 3.20/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1759,plain,
% 3.20/0.99      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1757,c_29]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1884,plain,
% 3.20/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_1759,c_1757]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,X1)
% 3.20/0.99      | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1130,plain,
% 3.20/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 3.20/0.99      | k1_xboole_0 = X3
% 3.20/0.99      | r2_hidden(X1,X3) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2525,plain,
% 3.20/0.99      ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1759,c_1130]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2758,plain,
% 3.20/0.99      ( sK2(X0) != sK6
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1884,c_2525]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3765,plain,
% 3.20/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.20/0.99      | sK6 != X0
% 3.20/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3759,c_2758]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4161,plain,
% 3.20/0.99      ( sK6 != X0
% 3.20/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3765,c_3366]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4165,plain,
% 3.20/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_4161]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1143,plain,
% 3.20/0.99      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_30,negated_conjecture,
% 3.20/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.20/0.99      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.20/0.99      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 3.20/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1611,plain,
% 3.20/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.20/0.99      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.20/0.99      | k2_mcart_1(sK6) = sK6 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_30,c_1608]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1752,plain,
% 3.20/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.20/0.99      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | k2_mcart_1(sK6) = sK6 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1611,c_1749]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1754,plain,
% 3.20/0.99      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | k2_mcart_1(sK6) = sK6 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_1752,c_1654]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1885,plain,
% 3.20/0.99      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.20/0.99      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | k2_mcart_1(sK6) = sK6 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1754,c_1759]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,plain,
% 3.20/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_28,plain,
% 3.20/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1173,plain,
% 3.20/0.99      ( k4_tarski(X0,X1) != X1 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_19,c_28]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1996,plain,
% 3.20/0.99      ( k2_mcart_1(sK6) != sK6 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1884,c_1173]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2059,plain,
% 3.20/0.99      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 3.20/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1885,c_1996]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2060,plain,
% 3.20/0.99      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.20/0.99      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_2059]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_22,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,X1)
% 3.20/0.99      | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1129,plain,
% 3.20/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 3.20/0.99      | k1_xboole_0 = X3
% 3.20/0.99      | r2_hidden(X0,X3) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1942,plain,
% 3.20/0.99      ( k4_tarski(sK6,X0) != sK2(X1)
% 3.20/0.99      | k1_xboole_0 = X1
% 3.20/0.99      | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1884,c_1129]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3773,plain,
% 3.20/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.20/0.99      | k4_tarski(sK6,X1) != X0
% 3.20/0.99      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3759,c_1942]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4339,plain,
% 3.20/0.99      ( k4_tarski(sK6,X0) != X1
% 3.20/0.99      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3773,c_3366]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4343,plain,
% 3.20/0.99      ( k1_mcart_1(sK6) != X0
% 3.20/0.99      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2060,c_4339]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5013,plain,
% 3.20/0.99      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.20/0.99      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4343,c_1136]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5017,plain,
% 3.20/0.99      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1143,c_5013]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5558,plain,
% 3.20/0.99      ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_4165,c_5017]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1141,plain,
% 3.20/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5560,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5558,c_1141]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.01
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.012
% 3.20/0.99  total_time:                             0.204
% 3.20/0.99  num_of_symbols:                         50
% 3.20/0.99  num_of_terms:                           6724
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    30
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        0
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        0
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       160
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        4
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        1
% 3.20/0.99  pred_elim:                              1
% 3.20/0.99  pred_elim_cl:                           1
% 3.20/0.99  pred_elim_cycles:                       3
% 3.20/0.99  merged_defs:                            8
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          8
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.003
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.
% 3.20/0.99  subtype_inf_time:                       0.
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                34
% 3.20/0.99  conjectures:                            4
% 3.20/0.99  epr:                                    3
% 3.20/0.99  horn:                                   24
% 3.20/0.99  ground:                                 4
% 3.20/0.99  unary:                                  13
% 3.20/0.99  binary:                                 6
% 3.20/0.99  lits:                                   81
% 3.20/0.99  lits_eq:                                60
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                7
% 3.20/0.99  fd_pseudo_cond:                         6
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      28
% 3.20/0.99  prop_fast_solver_calls:                 1104
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    1981
% 3.20/0.99  prop_preprocess_simplified:             7875
% 3.20/0.99  prop_fo_subsumed:                       34
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/0.99  prop_fast_solver_time:                  0.
% 3.20/0.99  prop_unsat_core_time:                   0.
% 3.20/0.99  
% 3.20/0.99  ------ QBF
% 3.20/0.99  
% 3.20/0.99  qbf_q_res:                              0
% 3.20/0.99  qbf_num_tautologies:                    0
% 3.20/0.99  qbf_prep_cycles:                        0
% 3.20/0.99  
% 3.20/0.99  ------ BMC1
% 3.20/0.99  
% 3.20/0.99  bmc1_current_bound:                     -1
% 3.20/0.99  bmc1_last_solved_bound:                 -1
% 3.20/0.99  bmc1_unsat_core_size:                   -1
% 3.20/0.99  bmc1_unsat_core_parents_size:           -1
% 3.20/0.99  bmc1_merge_next_fun:                    0
% 3.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation
% 3.20/0.99  
% 3.20/0.99  inst_num_of_clauses:                    873
% 3.20/0.99  inst_num_in_passive:                    395
% 3.20/0.99  inst_num_in_active:                     427
% 3.20/0.99  inst_num_in_unprocessed:                51
% 3.20/0.99  inst_num_of_loops:                      450
% 3.20/0.99  inst_num_of_learning_restarts:          0
% 3.20/0.99  inst_num_moves_active_passive:          22
% 3.20/0.99  inst_lit_activity:                      0
% 3.20/0.99  inst_lit_activity_moves:                0
% 3.20/0.99  inst_num_tautologies:                   0
% 3.20/0.99  inst_num_prop_implied:                  0
% 3.20/0.99  inst_num_existing_simplified:           0
% 3.20/0.99  inst_num_eq_res_simplified:             0
% 3.20/0.99  inst_num_child_elim:                    0
% 3.20/0.99  inst_num_of_dismatching_blockings:      124
% 3.20/0.99  inst_num_of_non_proper_insts:           834
% 3.20/0.99  inst_num_of_duplicates:                 0
% 3.20/0.99  inst_inst_num_from_inst_to_res:         0
% 3.20/0.99  inst_dismatching_checking_time:         0.
% 3.20/0.99  
% 3.20/0.99  ------ Resolution
% 3.20/0.99  
% 3.20/0.99  res_num_of_clauses:                     0
% 3.20/0.99  res_num_in_passive:                     0
% 3.20/0.99  res_num_in_active:                      0
% 3.20/0.99  res_num_of_loops:                       164
% 3.20/0.99  res_forward_subset_subsumed:            46
% 3.20/0.99  res_backward_subset_subsumed:           0
% 3.20/0.99  res_forward_subsumed:                   0
% 3.20/0.99  res_backward_subsumed:                  0
% 3.20/0.99  res_forward_subsumption_resolution:     0
% 3.20/0.99  res_backward_subsumption_resolution:    0
% 3.20/0.99  res_clause_to_clause_subsumption:       659
% 3.20/0.99  res_orphan_elimination:                 0
% 3.20/0.99  res_tautology_del:                      31
% 3.20/0.99  res_num_eq_res_simplified:              0
% 3.20/0.99  res_num_sel_changes:                    0
% 3.20/0.99  res_moves_from_active_to_pass:          0
% 3.20/0.99  
% 3.20/0.99  ------ Superposition
% 3.20/0.99  
% 3.20/0.99  sup_time_total:                         0.
% 3.20/0.99  sup_time_generating:                    0.
% 3.20/0.99  sup_time_sim_full:                      0.
% 3.20/0.99  sup_time_sim_immed:                     0.
% 3.20/0.99  
% 3.20/0.99  sup_num_of_clauses:                     103
% 3.20/0.99  sup_num_in_active:                      66
% 3.20/0.99  sup_num_in_passive:                     37
% 3.20/0.99  sup_num_of_loops:                       88
% 3.20/0.99  sup_fw_superposition:                   72
% 3.20/0.99  sup_bw_superposition:                   67
% 3.20/0.99  sup_immediate_simplified:               17
% 3.20/0.99  sup_given_eliminated:                   0
% 3.20/0.99  comparisons_done:                       0
% 3.20/0.99  comparisons_avoided:                    11
% 3.20/0.99  
% 3.20/0.99  ------ Simplifications
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  sim_fw_subset_subsumed:                 8
% 3.20/0.99  sim_bw_subset_subsumed:                 5
% 3.20/0.99  sim_fw_subsumed:                        5
% 3.20/0.99  sim_bw_subsumed:                        3
% 3.20/0.99  sim_fw_subsumption_res:                 10
% 3.20/0.99  sim_bw_subsumption_res:                 0
% 3.20/0.99  sim_tautology_del:                      0
% 3.20/0.99  sim_eq_tautology_del:                   12
% 3.20/0.99  sim_eq_res_simp:                        0
% 3.20/0.99  sim_fw_demodulated:                     1
% 3.20/0.99  sim_bw_demodulated:                     18
% 3.20/0.99  sim_light_normalised:                   4
% 3.20/0.99  sim_joinable_taut:                      0
% 3.20/0.99  sim_joinable_simp:                      0
% 3.20/0.99  sim_ac_normalised:                      0
% 3.20/0.99  sim_smt_subsumption:                    0
% 3.20/0.99  
%------------------------------------------------------------------------------
