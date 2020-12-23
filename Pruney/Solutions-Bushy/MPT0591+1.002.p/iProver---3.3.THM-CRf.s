%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0591+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:40 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of clauses        :   45 (  51 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 511 expanded)
%              Number of equality atoms :  103 ( 171 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3,f25])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
        | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 )
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
      | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 )
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f12,f29])).

fof(f47,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_636,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(X0,sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_23065,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK6(sK7),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_23068,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8
    | r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK6(sK7),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23065])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_660,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),X0),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7117,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_7120,plain,
    ( k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7117])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_626,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK6(X2)),k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(sK6(X2),X2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1167,plain,
    ( r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK6(X0)),k2_zfmisc_1(sK7,X0))
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | ~ r2_hidden(sK6(X0),X0) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_7116,plain,
    ( r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | ~ r2_hidden(sK6(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_7118,plain,
    ( r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7) != iProver_top
    | r2_hidden(sK6(sK8),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7116])).

cnf(c_8,plain,
    ( m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_171,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK6(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_172,plain,
    ( r2_hidden(sK6(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_186,plain,
    ( r2_hidden(sK6(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_172,c_13])).

cnf(c_6828,plain,
    ( r2_hidden(sK6(sK8),sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_6829,plain,
    ( k1_xboole_0 = sK8
    | r2_hidden(sK6(sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6828])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2461,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK1(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2462,plain,
    ( r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK1(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1137,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1138,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_650,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | r2_hidden(k4_tarski(X0,sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(X1,sK8)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_826,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | r2_hidden(k4_tarski(sK6(X0),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(X0,sK8))
    | ~ r2_hidden(sK6(X0),X0) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_827,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK6(X0),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(X0,sK8)) = iProver_top
    | r2_hidden(sK6(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK6(sK7),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | r2_hidden(sK6(sK7),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_659,plain,
    ( r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK1(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_665,plain,
    ( k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK1(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK7,sK8),sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_5,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_646,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_647,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8
    | r2_hidden(sK3(k2_zfmisc_1(sK7,sK8),sK8),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK3(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_173,plain,
    ( r2_hidden(sK6(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_175,plain,
    ( r2_hidden(sK6(sK7),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_17,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( k1_xboole_0 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23068,c_7120,c_7118,c_6829,c_2462,c_1138,c_829,c_665,c_647,c_175,c_19,c_14,c_15,c_16])).


%------------------------------------------------------------------------------
