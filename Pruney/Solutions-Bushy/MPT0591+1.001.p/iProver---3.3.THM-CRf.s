%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0591+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 124 expanded)
%              Number of clauses        :   37 (  40 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  260 ( 471 expanded)
%              Number of equality atoms :   87 ( 153 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
      | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 )
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f11,f28])).

fof(f44,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X2),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_662,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),X0),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10629,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK0(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_672,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),X0),k2_zfmisc_1(sK7,X1))
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1185,plain,
    ( r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK0(X0)),k2_zfmisc_1(sK7,X0))
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_10628,plain,
    ( r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK0(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | ~ r2_hidden(sK0(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_994,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(X0,sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2801,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK0(sK7),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2804,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8
    | r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK7),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2801])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2511,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK7,sK8),sK8),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2512,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK7,sK8),sK8),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2511])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1049,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK2(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_626,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK0(X2),X0),k2_zfmisc_1(X2,X1))
    | ~ r2_hidden(sK0(X2),X2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_999,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | r2_hidden(k4_tarski(sK0(X0),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(X0,sK8))
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1005,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(X0,sK8)) = iProver_top
    | r2_hidden(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_1007,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK7),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | r2_hidden(sK0(sK7),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_6,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_725,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8)
    | r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK7,sK8),sK8),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8))
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_726,plain,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK8
    | r2_hidden(sK4(k2_zfmisc_1(sK7,sK8),sK8),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK7,sK8),sK8),sK4(k2_zfmisc_1(sK7,sK8),sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_659,plain,
    ( r2_hidden(k4_tarski(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK2(k2_zfmisc_1(sK7,sK8),sK7)),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK7 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_160,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_651,plain,
    ( r2_hidden(sK0(sK8),sK8) ),
    inference(resolution,[status(thm)],[c_160,c_14])).

cnf(c_50,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_52,plain,
    ( r2_hidden(sK0(sK7),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_16,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( k1_xboole_0 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(sK7,sK8)) != sK8
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) != sK7 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10629,c_10628,c_2804,c_2512,c_1049,c_1007,c_726,c_659,c_651,c_52,c_18,c_13,c_15])).


%------------------------------------------------------------------------------
