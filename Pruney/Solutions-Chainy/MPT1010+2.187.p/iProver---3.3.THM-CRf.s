%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:37 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 429 expanded)
%              Number of clauses        :   43 (  57 expanded)
%              Number of leaves         :   20 ( 121 expanded)
%              Depth                    :   21
%              Number of atoms          :  391 (1245 expanded)
%              Number of equality atoms :  178 ( 554 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK6,sK5) != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_funct_1(sK6,sK5) != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f33])).

fof(f59,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f78,plain,(
    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f58,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f84,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f73])).

fof(f85,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f56,f68,f68,f68])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f55,f68,f68,f68])).

fof(f87,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f76])).

cnf(c_361,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_360,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1013,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_361,c_360])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_833,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(X0,X1)),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_823,plain,
    ( r2_hidden(sK1(k4_xboole_0(X0,X1)),X0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_999,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[status(thm)],[c_833,c_823])).

cnf(c_1577,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1013,c_999])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1750,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_1577,c_363])).

cnf(c_1752,plain,
    ( r2_hidden(sK4,k4_xboole_0(sK4,sK4))
    | ~ r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_200,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_201,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ v1_funct_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_205,plain,
    ( r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK6,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_20])).

cnf(c_206,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK6,X0),X2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X1
    | sK6 != sK6
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_206])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_271,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_234])).

cnf(c_617,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_761,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK5,sK3)
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_804,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4))
    | k1_funct_1(sK6,sK5) = X0
    | k1_funct_1(sK6,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_806,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_funct_1(sK6,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_810,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_17,c_16,c_761,c_806])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_620,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_815,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_620])).

cnf(c_816,plain,
    ( r2_hidden(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_815])).

cnf(c_51,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(sK4,sK4))
    | ~ r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_48,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(sK4,sK4))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_28,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1752,c_816,c_51,c_48,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:36:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.03/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.98  
% 3.03/0.98  ------  iProver source info
% 3.03/0.98  
% 3.03/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.98  git: non_committed_changes: false
% 3.03/0.98  git: last_make_outside_of_git: false
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  ------ Parsing...
% 3.03/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.98  ------ Proving...
% 3.03/0.98  ------ Problem Properties 
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  clauses                                 18
% 3.03/0.98  conjectures                             2
% 3.03/0.98  EPR                                     1
% 3.03/0.98  Horn                                    9
% 3.03/0.98  unary                                   5
% 3.03/0.98  binary                                  4
% 3.03/0.98  lits                                    42
% 3.03/0.98  lits eq                                 18
% 3.03/0.98  fd_pure                                 0
% 3.03/0.98  fd_pseudo                               0
% 3.03/0.98  fd_cond                                 1
% 3.03/0.98  fd_pseudo_cond                          7
% 3.03/0.98  AC symbols                              0
% 3.03/0.98  
% 3.03/0.98  ------ Input Options Time Limit: Unbounded
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  Current options:
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ Proving...
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  % SZS status Theorem for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  fof(f1,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f20,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.03/0.98    inference(nnf_transformation,[],[f1])).
% 3.03/0.98  
% 3.03/0.98  fof(f21,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.03/0.98    inference(flattening,[],[f20])).
% 3.03/0.98  
% 3.03/0.98  fof(f22,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.03/0.98    inference(rectify,[],[f21])).
% 3.03/0.98  
% 3.03/0.98  fof(f23,plain,(
% 3.03/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f24,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.03/0.98  
% 3.03/0.98  fof(f36,plain,(
% 3.03/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.03/0.98    inference(cnf_transformation,[],[f24])).
% 3.03/0.98  
% 3.03/0.98  fof(f80,plain,(
% 3.03/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.03/0.98    inference(equality_resolution,[],[f36])).
% 3.03/0.98  
% 3.03/0.98  fof(f2,axiom,(
% 3.03/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f15,plain,(
% 3.03/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.03/0.98    inference(ennf_transformation,[],[f2])).
% 3.03/0.98  
% 3.03/0.98  fof(f25,plain,(
% 3.03/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f26,plain,(
% 3.03/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).
% 3.03/0.98  
% 3.03/0.98  fof(f41,plain,(
% 3.03/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.03/0.98    inference(cnf_transformation,[],[f26])).
% 3.03/0.98  
% 3.03/0.98  fof(f35,plain,(
% 3.03/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.03/0.98    inference(cnf_transformation,[],[f24])).
% 3.03/0.98  
% 3.03/0.98  fof(f81,plain,(
% 3.03/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.03/0.98    inference(equality_resolution,[],[f35])).
% 3.03/0.98  
% 3.03/0.98  fof(f13,conjecture,(
% 3.03/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f14,negated_conjecture,(
% 3.03/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.03/0.99    inference(negated_conjecture,[],[f13])).
% 3.03/0.99  
% 3.03/0.99  fof(f18,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.03/0.99    inference(ennf_transformation,[],[f14])).
% 3.03/0.99  
% 3.03/0.99  fof(f19,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.03/0.99    inference(flattening,[],[f18])).
% 3.03/0.99  
% 3.03/0.99  fof(f33,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f34,plain,(
% 3.03/0.99    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f33])).
% 3.03/0.99  
% 3.03/0.99  fof(f59,plain,(
% 3.03/0.99    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f4,axiom,(
% 3.03/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f48,plain,(
% 3.03/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f4])).
% 3.03/0.99  
% 3.03/0.99  fof(f5,axiom,(
% 3.03/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f49,plain,(
% 3.03/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f5])).
% 3.03/0.99  
% 3.03/0.99  fof(f6,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f50,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f6])).
% 3.03/0.99  
% 3.03/0.99  fof(f7,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f51,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f7])).
% 3.03/0.99  
% 3.03/0.99  fof(f8,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f52,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f8])).
% 3.03/0.99  
% 3.03/0.99  fof(f9,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f53,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f9])).
% 3.03/0.99  
% 3.03/0.99  fof(f10,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f54,plain,(
% 3.03/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f10])).
% 3.03/0.99  
% 3.03/0.99  fof(f63,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f53,f54])).
% 3.03/0.99  
% 3.03/0.99  fof(f64,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f52,f63])).
% 3.03/0.99  
% 3.03/0.99  fof(f65,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f51,f64])).
% 3.03/0.99  
% 3.03/0.99  fof(f66,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f50,f65])).
% 3.03/0.99  
% 3.03/0.99  fof(f67,plain,(
% 3.03/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f49,f66])).
% 3.03/0.99  
% 3.03/0.99  fof(f68,plain,(
% 3.03/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f48,f67])).
% 3.03/0.99  
% 3.03/0.99  fof(f78,plain,(
% 3.03/0.99    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 3.03/0.99    inference(definition_unfolding,[],[f59,f68])).
% 3.03/0.99  
% 3.03/0.99  fof(f12,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f16,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.03/0.99    inference(ennf_transformation,[],[f12])).
% 3.03/0.99  
% 3.03/0.99  fof(f17,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.03/0.99    inference(flattening,[],[f16])).
% 3.03/0.99  
% 3.03/0.99  fof(f57,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f17])).
% 3.03/0.99  
% 3.03/0.99  fof(f60,plain,(
% 3.03/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f77,plain,(
% 3.03/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.03/0.99    inference(definition_unfolding,[],[f60,f68])).
% 3.03/0.99  
% 3.03/0.99  fof(f58,plain,(
% 3.03/0.99    v1_funct_1(sK6)),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f61,plain,(
% 3.03/0.99    r2_hidden(sK5,sK3)),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f62,plain,(
% 3.03/0.99    k1_funct_1(sK6,sK5) != sK4),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f3,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f27,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.03/0.99    inference(nnf_transformation,[],[f3])).
% 3.03/0.99  
% 3.03/0.99  fof(f28,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.03/0.99    inference(flattening,[],[f27])).
% 3.03/0.99  
% 3.03/0.99  fof(f29,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.03/0.99    inference(rectify,[],[f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f30,plain,(
% 3.03/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f31,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.03/0.99  
% 3.03/0.99  fof(f42,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f74,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.03/0.99    inference(definition_unfolding,[],[f42,f67])).
% 3.03/0.99  
% 3.03/0.99  fof(f86,plain,(
% 3.03/0.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.03/0.99    inference(equality_resolution,[],[f74])).
% 3.03/0.99  
% 3.03/0.99  fof(f43,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f73,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.03/0.99    inference(definition_unfolding,[],[f43,f67])).
% 3.03/0.99  
% 3.03/0.99  fof(f84,plain,(
% 3.03/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 3.03/0.99    inference(equality_resolution,[],[f73])).
% 3.03/0.99  
% 3.03/0.99  fof(f85,plain,(
% 3.03/0.99    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 3.03/0.99    inference(equality_resolution,[],[f84])).
% 3.03/0.99  
% 3.03/0.99  fof(f11,axiom,(
% 3.03/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f32,plain,(
% 3.03/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.03/0.99    inference(nnf_transformation,[],[f11])).
% 3.03/0.99  
% 3.03/0.99  fof(f56,plain,(
% 3.03/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.03/0.99    inference(cnf_transformation,[],[f32])).
% 3.03/0.99  
% 3.03/0.99  fof(f75,plain,(
% 3.03/0.99    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.03/0.99    inference(definition_unfolding,[],[f56,f68,f68,f68])).
% 3.03/0.99  
% 3.03/0.99  fof(f55,plain,(
% 3.03/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f32])).
% 3.03/0.99  
% 3.03/0.99  fof(f76,plain,(
% 3.03/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.03/0.99    inference(definition_unfolding,[],[f55,f68,f68,f68])).
% 3.03/0.99  
% 3.03/0.99  fof(f87,plain,(
% 3.03/0.99    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.03/0.99    inference(equality_resolution,[],[f76])).
% 3.03/0.99  
% 3.03/0.99  cnf(c_361,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_360,plain,( X0 = X0 ),theory(equality) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1013,plain,
% 3.03/0.99      ( X0 != X1 | X1 = X0 ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_361,c_360]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_6,plain,
% 3.03/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.03/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_833,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(k4_xboole_0(X0,X1)),X1)
% 3.03/0.99      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_5,plain,
% 3.03/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_823,plain,
% 3.03/0.99      ( r2_hidden(sK1(k4_xboole_0(X0,X1)),X0)
% 3.03/0.99      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_5,c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_999,plain,
% 3.03/0.99      ( k1_xboole_0 = k4_xboole_0(X0,X0) ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_833,c_823]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1577,plain,
% 3.03/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_1013,c_999]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_363,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.03/0.99      theory(equality) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1750,plain,
% 3.03/0.99      ( r2_hidden(X0,k4_xboole_0(X1,X1))
% 3.03/0.99      | ~ r2_hidden(X2,k1_xboole_0)
% 3.03/0.99      | X0 != X2 ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_1577,c_363]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1752,plain,
% 3.03/0.99      ( r2_hidden(sK4,k4_xboole_0(sK4,sK4))
% 3.03/0.99      | ~ r2_hidden(sK4,k1_xboole_0)
% 3.03/0.99      | sK4 != sK4 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1750]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_19,negated_conjecture,
% 3.03/0.99      ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_15,plain,
% 3.03/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | ~ r2_hidden(X3,X1)
% 3.03/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.03/0.99      | ~ v1_funct_1(X0)
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_18,negated_conjecture,
% 3.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_200,plain,
% 3.03/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/0.99      | ~ r2_hidden(X3,X1)
% 3.03/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.03/0.99      | ~ v1_funct_1(X0)
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.03/0.99      | sK6 != X0
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_201,plain,
% 3.03/0.99      ( ~ v1_funct_2(sK6,X0,X1)
% 3.03/0.99      | ~ r2_hidden(X2,X0)
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.03/0.99      | ~ v1_funct_1(sK6)
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.03/0.99      | k1_xboole_0 = X1 ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_20,negated_conjecture,
% 3.03/0.99      ( v1_funct_1(sK6) ),
% 3.03/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_205,plain,
% 3.03/0.99      ( r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.03/0.99      | ~ r2_hidden(X2,X0)
% 3.03/0.99      | ~ v1_funct_2(sK6,X0,X1)
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.03/0.99      | k1_xboole_0 = X1 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_201,c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_206,plain,
% 3.03/0.99      ( ~ v1_funct_2(sK6,X0,X1)
% 3.03/0.99      | ~ r2_hidden(X2,X0)
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.03/0.99      | k1_xboole_0 = X1 ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_205]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_233,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,X1)
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X0),X2)
% 3.03/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X2
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.03/0.99      | sK3 != X1
% 3.03/0.99      | sK6 != sK6
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_206]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_234,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,sK3)
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.03/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 3.03/0.99      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_271,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,sK3)
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.03/0.99      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_234]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_617,plain,
% 3.03/0.99      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 3.03/0.99      | r2_hidden(X0,sK3) != iProver_top
% 3.03/0.99      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_17,negated_conjecture,
% 3.03/0.99      ( r2_hidden(sK5,sK3) ),
% 3.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_16,negated_conjecture,
% 3.03/0.99      ( k1_funct_1(sK6,sK5) != sK4 ),
% 3.03/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_761,plain,
% 3.03/0.99      ( r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.03/0.99      | ~ r2_hidden(sK5,sK3)
% 3.03/0.99      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_271]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_12,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.03/0.99      | X0 = X1
% 3.03/0.99      | X0 = X2 ),
% 3.03/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_804,plain,
% 3.03/0.99      ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4))
% 3.03/0.99      | k1_funct_1(sK6,sK5) = X0
% 3.03/0.99      | k1_funct_1(sK6,sK5) = sK4 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_806,plain,
% 3.03/0.99      ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.03/0.99      | k1_funct_1(sK6,sK5) = sK4 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_804]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_810,plain,
% 3.03/0.99      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_617,c_17,c_16,c_761,c_806]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_11,plain,
% 3.03/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_620,plain,
% 3.03/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_815,plain,
% 3.03/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_810,c_620]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_816,plain,
% 3.03/0.99      ( r2_hidden(sK4,k1_xboole_0) ),
% 3.03/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_815]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_51,plain,
% 3.03/0.99      ( ~ r2_hidden(sK4,k4_xboole_0(sK4,sK4)) | ~ r2_hidden(sK4,sK4) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_48,plain,
% 3.03/0.99      ( ~ r2_hidden(sK4,k4_xboole_0(sK4,sK4)) | r2_hidden(sK4,sK4) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_13,plain,
% 3.03/0.99      ( X0 = X1
% 3.03/0.99      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_29,plain,
% 3.03/0.99      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 3.03/0.99      | sK4 = sK4 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_14,plain,
% 3.03/0.99      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_28,plain,
% 3.03/0.99      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(contradiction,plain,
% 3.03/0.99      ( $false ),
% 3.03/0.99      inference(minisat,[status(thm)],[c_1752,c_816,c_51,c_48,c_29,c_28]) ).
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  ------                               Statistics
% 3.03/0.99  
% 3.03/0.99  ------ Selected
% 3.03/0.99  
% 3.03/0.99  total_time:                             0.123
% 3.03/0.99  
%------------------------------------------------------------------------------
