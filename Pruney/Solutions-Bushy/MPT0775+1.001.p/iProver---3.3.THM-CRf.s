%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0775+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:06 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 318 expanded)
%              Number of clauses        :   54 ( 101 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  350 (1389 expanded)
%              Number of equality atoms :  121 ( 238 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v8_relat_2(X1)
         => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ~ v8_relat_2(k2_wellord1(X1,X0))
        & v8_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v8_relat_2(k2_wellord1(sK5,sK4))
      & v8_relat_2(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v8_relat_2(k2_wellord1(sK5,sK4))
    & v8_relat_2(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f25])).

fof(f42,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f21])).

fof(f38,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f35,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    v8_relat_2(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ~ v8_relat_2(k2_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_638,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_628,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_639,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1454,plain,
    ( k3_xboole_0(sK5,k2_zfmisc_1(X0,X0)) = k2_wellord1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_628,c_639])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_642,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_637,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) != iProver_top
    | v8_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2223,plain,
    ( r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1)),sK3(k3_xboole_0(X0,X1))),X1) != iProver_top
    | r2_hidden(k4_tarski(sK1(k3_xboole_0(X0,X1)),sK3(k3_xboole_0(X0,X1))),X0) != iProver_top
    | v8_relat_2(k3_xboole_0(X0,X1)) = iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_637])).

cnf(c_15027,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),k2_zfmisc_1(X0,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k3_xboole_0(sK5,k2_zfmisc_1(X0,X0))),sK3(k3_xboole_0(sK5,k2_zfmisc_1(X0,X0)))),sK5) != iProver_top
    | v8_relat_2(k3_xboole_0(sK5,k2_zfmisc_1(X0,X0))) = iProver_top
    | v1_relat_1(k3_xboole_0(sK5,k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_2223])).

cnf(c_15034,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),k2_zfmisc_1(X0,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) != iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15027,c_1454])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_636,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) = iProver_top
    | v8_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_641,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1459,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_641])).

cnf(c_2020,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),k2_zfmisc_1(X0,X0)) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_1459])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2100,plain,
    ( r2_hidden(sK3(k2_wellord1(sK5,X0)),X0) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2020,c_632])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_635,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) = iProver_top
    | v8_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2021,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),k2_zfmisc_1(X0,X0)) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_1459])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_631,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2130,plain,
    ( r2_hidden(sK1(k2_wellord1(sK5,X0)),X0) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_631])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_633,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2220,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X1)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_642])).

cnf(c_2375,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_wellord1(sK5,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_2220])).

cnf(c_2396,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) != iProver_top
    | r2_hidden(sK3(k2_wellord1(sK5,X0)),X0) != iProver_top
    | r2_hidden(sK1(k2_wellord1(sK5,X0)),X0) != iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_637])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_640,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1460,plain,
    ( r2_hidden(X0,k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_640])).

cnf(c_1965,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_1460])).

cnf(c_1964,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_1460])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_634,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),X2) = iProver_top
    | v8_relat_2(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2029,plain,
    ( r2_hidden(k4_tarski(X0,sK2(k2_wellord1(sK5,X1))),sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(k2_wellord1(sK5,X1))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X1)) = iProver_top
    | v8_relat_2(sK5) != iProver_top
    | v1_relat_1(k2_wellord1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_634])).

cnf(c_18,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v8_relat_2(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v8_relat_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8726,plain,
    ( v1_relat_1(k2_wellord1(sK5,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(k2_wellord1(sK5,X1))),sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(k2_wellord1(sK5,X1))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2029,c_18,c_19])).

cnf(c_8727,plain,
    ( r2_hidden(k4_tarski(X0,sK2(k2_wellord1(sK5,X1))),sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(k2_wellord1(sK5,X1))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X1)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8726])).

cnf(c_8732,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_8727])).

cnf(c_17000,plain,
    ( v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15034,c_2100,c_2130,c_2396,c_8732])).

cnf(c_17006,plain,
    ( v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_17000])).

cnf(c_17985,plain,
    ( v8_relat_2(k2_wellord1(sK5,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17006,c_18])).

cnf(c_15,negated_conjecture,
    ( ~ v8_relat_2(k2_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_630,plain,
    ( v8_relat_2(k2_wellord1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17991,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_17985,c_630])).


%------------------------------------------------------------------------------
