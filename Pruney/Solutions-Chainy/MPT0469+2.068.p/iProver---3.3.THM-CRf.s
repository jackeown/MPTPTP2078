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
% DateTime   : Thu Dec  3 11:43:54 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 122 expanded)
%              Number of clauses        :   30 (  39 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 ( 348 expanded)
%              Number of equality atoms :   82 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK4(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4635,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2373,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1361,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),sK0(k2_relat_1(k1_xboole_0),k1_xboole_0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_884,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7,c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_891,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_884,c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_895,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_884,c_11])).

cnf(c_1259,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_891,c_895])).

cnf(c_1003,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k1_xboole_0)
    | ~ r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_845,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_relat_1(k1_xboole_0))
    | r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_714,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k2_tarski(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),sK0(k2_relat_1(k1_xboole_0),k1_xboole_0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_686,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_relat_1(k1_xboole_0))
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_184,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_681,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_682,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_638,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_640,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_40,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4635,c_2373,c_1361,c_1259,c_1003,c_845,c_714,c_686,c_682,c_640,c_40,c_39,c_19,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.36/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/0.97  
% 2.36/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.97  
% 2.36/0.97  ------  iProver source info
% 2.36/0.97  
% 2.36/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.97  git: non_committed_changes: false
% 2.36/0.97  git: last_make_outside_of_git: false
% 2.36/0.97  
% 2.36/0.97  ------ 
% 2.36/0.97  ------ Parsing...
% 2.36/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.97  
% 2.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.36/0.97  
% 2.36/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.97  
% 2.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.97  ------ Proving...
% 2.36/0.97  ------ Problem Properties 
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  clauses                                 15
% 2.36/0.97  conjectures                             1
% 2.36/0.97  EPR                                     0
% 2.36/0.97  Horn                                    11
% 2.36/0.97  unary                                   4
% 2.36/0.97  binary                                  5
% 2.36/0.97  lits                                    32
% 2.36/0.97  lits eq                                 14
% 2.36/0.97  fd_pure                                 0
% 2.36/0.97  fd_pseudo                               0
% 2.36/0.97  fd_cond                                 1
% 2.36/0.97  fd_pseudo_cond                          4
% 2.36/0.97  AC symbols                              0
% 2.36/0.97  
% 2.36/0.97  ------ Input Options Time Limit: Unbounded
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  ------ 
% 2.36/0.97  Current options:
% 2.36/0.97  ------ 
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  ------ Proving...
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  % SZS status Theorem for theBenchmark.p
% 2.36/0.97  
% 2.36/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.97  
% 2.36/0.97  fof(f2,axiom,(
% 2.36/0.97    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f31,plain,(
% 2.36/0.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f2])).
% 2.36/0.97  
% 2.36/0.97  fof(f5,axiom,(
% 2.36/0.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f20,plain,(
% 2.36/0.97    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.36/0.97    inference(nnf_transformation,[],[f5])).
% 2.36/0.97  
% 2.36/0.97  fof(f36,plain,(
% 2.36/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.36/0.97    inference(cnf_transformation,[],[f20])).
% 2.36/0.97  
% 2.36/0.97  fof(f3,axiom,(
% 2.36/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f32,plain,(
% 2.36/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f3])).
% 2.36/0.97  
% 2.36/0.97  fof(f46,plain,(
% 2.36/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 2.36/0.97    inference(definition_unfolding,[],[f36,f32])).
% 2.36/0.97  
% 2.36/0.97  fof(f1,axiom,(
% 2.36/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f11,plain,(
% 2.36/0.97    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.36/0.97    inference(ennf_transformation,[],[f1])).
% 2.36/0.97  
% 2.36/0.97  fof(f15,plain,(
% 2.36/0.97    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.36/0.97    inference(nnf_transformation,[],[f11])).
% 2.36/0.97  
% 2.36/0.97  fof(f16,plain,(
% 2.36/0.97    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f17,plain,(
% 2.36/0.97    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.36/0.97  
% 2.36/0.97  fof(f29,plain,(
% 2.36/0.97    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f17])).
% 2.36/0.97  
% 2.36/0.97  fof(f6,axiom,(
% 2.36/0.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f21,plain,(
% 2.36/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.36/0.97    inference(nnf_transformation,[],[f6])).
% 2.36/0.97  
% 2.36/0.97  fof(f22,plain,(
% 2.36/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.36/0.97    inference(rectify,[],[f21])).
% 2.36/0.97  
% 2.36/0.97  fof(f25,plain,(
% 2.36/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f24,plain,(
% 2.36/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f23,plain,(
% 2.36/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f26,plain,(
% 2.36/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 2.36/0.97  
% 2.36/0.97  fof(f38,plain,(
% 2.36/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.36/0.97    inference(cnf_transformation,[],[f26])).
% 2.36/0.97  
% 2.36/0.97  fof(f50,plain,(
% 2.36/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.36/0.97    inference(equality_resolution,[],[f38])).
% 2.36/0.97  
% 2.36/0.97  fof(f8,axiom,(
% 2.36/0.97    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f12,plain,(
% 2.36/0.97    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.36/0.97    inference(ennf_transformation,[],[f8])).
% 2.36/0.97  
% 2.36/0.97  fof(f13,plain,(
% 2.36/0.97    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.36/0.97    inference(flattening,[],[f12])).
% 2.36/0.97  
% 2.36/0.97  fof(f27,plain,(
% 2.36/0.97    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK4(X1),k1_relat_1(X1)))),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f28,plain,(
% 2.36/0.97    ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f27])).
% 2.36/0.97  
% 2.36/0.97  fof(f43,plain,(
% 2.36/0.97    ( ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f28])).
% 2.36/0.97  
% 2.36/0.97  fof(f4,axiom,(
% 2.36/0.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f18,plain,(
% 2.36/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.36/0.97    inference(nnf_transformation,[],[f4])).
% 2.36/0.97  
% 2.36/0.97  fof(f19,plain,(
% 2.36/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.36/0.97    inference(flattening,[],[f18])).
% 2.36/0.97  
% 2.36/0.97  fof(f34,plain,(
% 2.36/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.36/0.97    inference(cnf_transformation,[],[f19])).
% 2.36/0.97  
% 2.36/0.97  fof(f48,plain,(
% 2.36/0.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.36/0.97    inference(equality_resolution,[],[f34])).
% 2.36/0.97  
% 2.36/0.97  fof(f33,plain,(
% 2.36/0.97    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f19])).
% 2.36/0.97  
% 2.36/0.97  fof(f7,axiom,(
% 2.36/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f42,plain,(
% 2.36/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.36/0.97    inference(cnf_transformation,[],[f7])).
% 2.36/0.97  
% 2.36/0.97  fof(f9,conjecture,(
% 2.36/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f10,negated_conjecture,(
% 2.36/0.97    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.36/0.97    inference(negated_conjecture,[],[f9])).
% 2.36/0.97  
% 2.36/0.97  fof(f14,plain,(
% 2.36/0.97    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.36/0.97    inference(ennf_transformation,[],[f10])).
% 2.36/0.97  
% 2.36/0.97  fof(f44,plain,(
% 2.36/0.97    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.36/0.97    inference(cnf_transformation,[],[f14])).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2,plain,
% 2.36/0.97      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.36/0.97      inference(cnf_transformation,[],[f31]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_4635,plain,
% 2.36/0.97      ( k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))))) = k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_7,plain,
% 2.36/0.97      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
% 2.36/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2373,plain,
% 2.36/0.97      ( ~ r2_hidden(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k1_xboole_0)
% 2.36/0.97      | k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))))) != k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1361,plain,
% 2.36/0.97      ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),sK0(k2_relat_1(k1_xboole_0),k1_xboole_0))) = k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_884,plain,
% 2.36/0.97      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.36/0.97      inference(resolution,[status(thm)],[c_7,c_2]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1,plain,
% 2.36/0.97      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.36/0.97      inference(cnf_transformation,[],[f29]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_891,plain,
% 2.36/0.97      ( r2_hidden(sK0(X0,k1_xboole_0),X0) | k1_xboole_0 = X0 ),
% 2.36/0.97      inference(resolution,[status(thm)],[c_884,c_1]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_11,plain,
% 2.36/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.36/0.97      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.36/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_895,plain,
% 2.36/0.97      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 2.36/0.97      inference(resolution,[status(thm)],[c_884,c_11]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1259,plain,
% 2.36/0.97      ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.36/0.97      inference(resolution,[status(thm)],[c_891,c_895]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1003,plain,
% 2.36/0.97      ( r2_hidden(k4_tarski(sK4(k1_xboole_0),sK3(k1_xboole_0,sK4(k1_xboole_0))),k1_xboole_0)
% 2.36/0.97      | ~ r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_13,plain,
% 2.36/0.97      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.36/0.97      | r2_hidden(sK4(X1),k1_relat_1(X1))
% 2.36/0.97      | ~ v1_relat_1(X1) ),
% 2.36/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_845,plain,
% 2.36/0.97      ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_relat_1(k1_xboole_0))
% 2.36/0.97      | r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 2.36/0.97      | ~ v1_relat_1(k1_xboole_0) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_714,plain,
% 2.36/0.97      ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.36/0.97      | k4_xboole_0(k1_xboole_0,k2_tarski(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),sK0(k2_relat_1(k1_xboole_0),k1_xboole_0))) != k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_686,plain,
% 2.36/0.97      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_relat_1(k1_xboole_0))
% 2.36/0.97      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.36/0.97      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_184,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_681,plain,
% 2.36/0.97      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_184]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_682,plain,
% 2.36/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.36/0.97      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.36/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_681]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_190,plain,
% 2.36/0.97      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.36/0.97      theory(equality) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_638,plain,
% 2.36/0.97      ( v1_relat_1(X0)
% 2.36/0.97      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 2.36/0.97      | X0 != k2_zfmisc_1(X1,X2) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_190]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_640,plain,
% 2.36/0.97      ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.36/0.97      | v1_relat_1(k1_xboole_0)
% 2.36/0.97      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_638]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_4,plain,
% 2.36/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.36/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_40,plain,
% 2.36/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_5,plain,
% 2.36/0.97      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.36/0.97      | k1_xboole_0 = X1
% 2.36/0.97      | k1_xboole_0 = X0 ),
% 2.36/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_39,plain,
% 2.36/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.36/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_12,plain,
% 2.36/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.36/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_19,plain,
% 2.36/0.97      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_14,negated_conjecture,
% 2.36/0.97      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.36/0.97      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(contradiction,plain,
% 2.36/0.97      ( $false ),
% 2.36/0.97      inference(minisat,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_4635,c_2373,c_1361,c_1259,c_1003,c_845,c_714,c_686,
% 2.36/0.97                 c_682,c_640,c_40,c_39,c_19,c_14]) ).
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.97  
% 2.36/0.97  ------                               Statistics
% 2.36/0.97  
% 2.36/0.97  ------ Selected
% 2.36/0.97  
% 2.36/0.97  total_time:                             0.192
% 2.36/0.97  
%------------------------------------------------------------------------------
