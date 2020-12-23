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
% DateTime   : Thu Dec  3 11:49:26 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 633 expanded)
%              Number of clauses        :   57 ( 219 expanded)
%              Number of leaves         :   12 ( 148 expanded)
%              Depth                    :   23
%              Number of atoms          :  366 (3032 expanded)
%              Number of equality atoms :  215 (1612 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f22])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK1(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK1(X0,X1)) = X0
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK1(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK1(X0,X1)) = X0
      & v1_funct_1(sK1(X0,X1))
      & v1_relat_1(sK1(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f20])).

fof(f39,plain,(
    ! [X0,X1] : k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK3
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK3
              | k1_relat_1(X1) != sK3
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_xboole_0 != sK3
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK3
            | k1_relat_1(X1) != sK3
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f24])).

fof(f45,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK3
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] : v1_funct_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK1(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f44,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_16,plain,
    ( k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_434,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_845,plain,
    ( sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK1(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_434])).

cnf(c_14,plain,
    ( v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_34,plain,
    ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( v1_funct_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_37,plain,
    ( v1_funct_1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_989,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_34,c_37])).

cnf(c_990,plain,
    ( sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_989])).

cnf(c_1001,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X2
    | sK3 != X0
    | v1_relat_1(sK2(X2)) != iProver_top
    | v1_funct_1(sK2(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_990])).

cnf(c_602,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_434])).

cnf(c_18,plain,
    ( v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24,plain,
    ( v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,plain,
    ( v1_funct_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_755,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_24,c_27])).

cnf(c_756,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_844,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2
    | v1_relat_1(sK1(X0,X1)) != iProver_top
    | v1_funct_1(sK1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_756])).

cnf(c_870,plain,
    ( ~ v1_relat_1(sK1(X0,X1))
    | ~ v1_funct_1(sK1(X0,X1))
    | sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_844])).

cnf(c_1094,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X2
    | sK3 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1001,c_14,c_13,c_870])).

cnf(c_1095,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2 ),
    inference(renaming,[status(thm)],[c_1094])).

cnf(c_1100,plain,
    ( sK1(sK3,X0) = sK2(X1)
    | sK3 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1095])).

cnf(c_1208,plain,
    ( sK1(sK3,X0) = sK2(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1100])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_445,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_441,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1435,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_441])).

cnf(c_2203,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_445,c_1435])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2213,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2203,c_6])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK1(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_440,plain,
    ( k1_funct_1(sK1(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2393,plain,
    ( k1_funct_1(sK1(X0,X1),sK0(k1_xboole_0,X2,X0)) = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2213,c_440])).

cnf(c_2909,plain,
    ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = X1
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1208,c_2393])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_47,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_174,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_596,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_597,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_3064,plain,
    ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2909,c_19,c_47,c_48,c_597])).

cnf(c_3111,plain,
    ( k1_relat_1(k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3))) = X1 ),
    inference(superposition,[status(thm)],[c_3064,c_12])).

cnf(c_3114,plain,
    ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3064,c_8])).

cnf(c_3709,plain,
    ( k1_relat_1(k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3111,c_3114])).

cnf(c_3751,plain,
    ( sK2(X0) = k1_relat_1(k1_xboole_0)
    | sK3 != X1
    | sK3 != X0 ),
    inference(demodulation,[status(thm)],[c_3709,c_1095])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK2(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_437,plain,
    ( k1_funct_1(sK2(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2394,plain,
    ( k1_funct_1(sK2(X0),sK0(k1_xboole_0,X1,X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2213,c_437])).

cnf(c_3085,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3064,c_2394])).

cnf(c_4506,plain,
    ( sK3 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3751,c_19,c_47,c_48,c_596,c_597,c_3085])).

cnf(c_4510,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_4506])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.76/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.00  
% 2.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/1.00  
% 2.76/1.00  ------  iProver source info
% 2.76/1.00  
% 2.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/1.00  git: non_committed_changes: false
% 2.76/1.00  git: last_make_outside_of_git: false
% 2.76/1.00  
% 2.76/1.00  ------ 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options
% 2.76/1.00  
% 2.76/1.00  --out_options                           all
% 2.76/1.00  --tptp_safe_out                         true
% 2.76/1.00  --problem_path                          ""
% 2.76/1.00  --include_path                          ""
% 2.76/1.00  --clausifier                            res/vclausify_rel
% 2.76/1.00  --clausifier_options                    --mode clausify
% 2.76/1.00  --stdin                                 false
% 2.76/1.00  --stats_out                             all
% 2.76/1.00  
% 2.76/1.00  ------ General Options
% 2.76/1.00  
% 2.76/1.00  --fof                                   false
% 2.76/1.00  --time_out_real                         305.
% 2.76/1.00  --time_out_virtual                      -1.
% 2.76/1.00  --symbol_type_check                     false
% 2.76/1.00  --clausify_out                          false
% 2.76/1.00  --sig_cnt_out                           false
% 2.76/1.00  --trig_cnt_out                          false
% 2.76/1.00  --trig_cnt_out_tolerance                1.
% 2.76/1.00  --trig_cnt_out_sk_spl                   false
% 2.76/1.00  --abstr_cl_out                          false
% 2.76/1.00  
% 2.76/1.00  ------ Global Options
% 2.76/1.00  
% 2.76/1.00  --schedule                              default
% 2.76/1.00  --add_important_lit                     false
% 2.76/1.00  --prop_solver_per_cl                    1000
% 2.76/1.00  --min_unsat_core                        false
% 2.76/1.00  --soft_assumptions                      false
% 2.76/1.00  --soft_lemma_size                       3
% 2.76/1.00  --prop_impl_unit_size                   0
% 2.76/1.00  --prop_impl_unit                        []
% 2.76/1.00  --share_sel_clauses                     true
% 2.76/1.00  --reset_solvers                         false
% 2.76/1.00  --bc_imp_inh                            [conj_cone]
% 2.76/1.00  --conj_cone_tolerance                   3.
% 2.76/1.00  --extra_neg_conj                        none
% 2.76/1.00  --large_theory_mode                     true
% 2.76/1.00  --prolific_symb_bound                   200
% 2.76/1.00  --lt_threshold                          2000
% 2.76/1.00  --clause_weak_htbl                      true
% 2.76/1.00  --gc_record_bc_elim                     false
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing Options
% 2.76/1.00  
% 2.76/1.00  --preprocessing_flag                    true
% 2.76/1.00  --time_out_prep_mult                    0.1
% 2.76/1.00  --splitting_mode                        input
% 2.76/1.00  --splitting_grd                         true
% 2.76/1.00  --splitting_cvd                         false
% 2.76/1.00  --splitting_cvd_svl                     false
% 2.76/1.00  --splitting_nvd                         32
% 2.76/1.00  --sub_typing                            true
% 2.76/1.00  --prep_gs_sim                           true
% 2.76/1.00  --prep_unflatten                        true
% 2.76/1.00  --prep_res_sim                          true
% 2.76/1.00  --prep_upred                            true
% 2.76/1.00  --prep_sem_filter                       exhaustive
% 2.76/1.00  --prep_sem_filter_out                   false
% 2.76/1.00  --pred_elim                             true
% 2.76/1.00  --res_sim_input                         true
% 2.76/1.00  --eq_ax_congr_red                       true
% 2.76/1.00  --pure_diseq_elim                       true
% 2.76/1.00  --brand_transform                       false
% 2.76/1.00  --non_eq_to_eq                          false
% 2.76/1.00  --prep_def_merge                        true
% 2.76/1.00  --prep_def_merge_prop_impl              false
% 2.76/1.00  --prep_def_merge_mbd                    true
% 2.76/1.00  --prep_def_merge_tr_red                 false
% 2.76/1.00  --prep_def_merge_tr_cl                  false
% 2.76/1.00  --smt_preprocessing                     true
% 2.76/1.00  --smt_ac_axioms                         fast
% 2.76/1.00  --preprocessed_out                      false
% 2.76/1.00  --preprocessed_stats                    false
% 2.76/1.00  
% 2.76/1.00  ------ Abstraction refinement Options
% 2.76/1.00  
% 2.76/1.00  --abstr_ref                             []
% 2.76/1.00  --abstr_ref_prep                        false
% 2.76/1.00  --abstr_ref_until_sat                   false
% 2.76/1.00  --abstr_ref_sig_restrict                funpre
% 2.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.00  --abstr_ref_under                       []
% 2.76/1.00  
% 2.76/1.00  ------ SAT Options
% 2.76/1.00  
% 2.76/1.00  --sat_mode                              false
% 2.76/1.00  --sat_fm_restart_options                ""
% 2.76/1.00  --sat_gr_def                            false
% 2.76/1.00  --sat_epr_types                         true
% 2.76/1.00  --sat_non_cyclic_types                  false
% 2.76/1.00  --sat_finite_models                     false
% 2.76/1.00  --sat_fm_lemmas                         false
% 2.76/1.00  --sat_fm_prep                           false
% 2.76/1.00  --sat_fm_uc_incr                        true
% 2.76/1.00  --sat_out_model                         small
% 2.76/1.00  --sat_out_clauses                       false
% 2.76/1.00  
% 2.76/1.00  ------ QBF Options
% 2.76/1.00  
% 2.76/1.00  --qbf_mode                              false
% 2.76/1.00  --qbf_elim_univ                         false
% 2.76/1.00  --qbf_dom_inst                          none
% 2.76/1.00  --qbf_dom_pre_inst                      false
% 2.76/1.00  --qbf_sk_in                             false
% 2.76/1.00  --qbf_pred_elim                         true
% 2.76/1.00  --qbf_split                             512
% 2.76/1.00  
% 2.76/1.00  ------ BMC1 Options
% 2.76/1.00  
% 2.76/1.00  --bmc1_incremental                      false
% 2.76/1.00  --bmc1_axioms                           reachable_all
% 2.76/1.00  --bmc1_min_bound                        0
% 2.76/1.00  --bmc1_max_bound                        -1
% 2.76/1.00  --bmc1_max_bound_default                -1
% 2.76/1.00  --bmc1_symbol_reachability              true
% 2.76/1.00  --bmc1_property_lemmas                  false
% 2.76/1.00  --bmc1_k_induction                      false
% 2.76/1.00  --bmc1_non_equiv_states                 false
% 2.76/1.00  --bmc1_deadlock                         false
% 2.76/1.00  --bmc1_ucm                              false
% 2.76/1.00  --bmc1_add_unsat_core                   none
% 2.76/1.00  --bmc1_unsat_core_children              false
% 2.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.00  --bmc1_out_stat                         full
% 2.76/1.00  --bmc1_ground_init                      false
% 2.76/1.00  --bmc1_pre_inst_next_state              false
% 2.76/1.00  --bmc1_pre_inst_state                   false
% 2.76/1.00  --bmc1_pre_inst_reach_state             false
% 2.76/1.00  --bmc1_out_unsat_core                   false
% 2.76/1.00  --bmc1_aig_witness_out                  false
% 2.76/1.00  --bmc1_verbose                          false
% 2.76/1.00  --bmc1_dump_clauses_tptp                false
% 2.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.00  --bmc1_dump_file                        -
% 2.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.00  --bmc1_ucm_extend_mode                  1
% 2.76/1.00  --bmc1_ucm_init_mode                    2
% 2.76/1.00  --bmc1_ucm_cone_mode                    none
% 2.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.00  --bmc1_ucm_relax_model                  4
% 2.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.00  --bmc1_ucm_layered_model                none
% 2.76/1.00  --bmc1_ucm_max_lemma_size               10
% 2.76/1.00  
% 2.76/1.00  ------ AIG Options
% 2.76/1.00  
% 2.76/1.00  --aig_mode                              false
% 2.76/1.00  
% 2.76/1.00  ------ Instantiation Options
% 2.76/1.00  
% 2.76/1.00  --instantiation_flag                    true
% 2.76/1.00  --inst_sos_flag                         false
% 2.76/1.00  --inst_sos_phase                        true
% 2.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel_side                     num_symb
% 2.76/1.00  --inst_solver_per_active                1400
% 2.76/1.00  --inst_solver_calls_frac                1.
% 2.76/1.00  --inst_passive_queue_type               priority_queues
% 2.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.00  --inst_passive_queues_freq              [25;2]
% 2.76/1.00  --inst_dismatching                      true
% 2.76/1.00  --inst_eager_unprocessed_to_passive     true
% 2.76/1.00  --inst_prop_sim_given                   true
% 2.76/1.00  --inst_prop_sim_new                     false
% 2.76/1.00  --inst_subs_new                         false
% 2.76/1.00  --inst_eq_res_simp                      false
% 2.76/1.00  --inst_subs_given                       false
% 2.76/1.00  --inst_orphan_elimination               true
% 2.76/1.00  --inst_learning_loop_flag               true
% 2.76/1.00  --inst_learning_start                   3000
% 2.76/1.00  --inst_learning_factor                  2
% 2.76/1.00  --inst_start_prop_sim_after_learn       3
% 2.76/1.00  --inst_sel_renew                        solver
% 2.76/1.00  --inst_lit_activity_flag                true
% 2.76/1.00  --inst_restr_to_given                   false
% 2.76/1.00  --inst_activity_threshold               500
% 2.76/1.00  --inst_out_proof                        true
% 2.76/1.00  
% 2.76/1.00  ------ Resolution Options
% 2.76/1.00  
% 2.76/1.00  --resolution_flag                       true
% 2.76/1.00  --res_lit_sel                           adaptive
% 2.76/1.00  --res_lit_sel_side                      none
% 2.76/1.00  --res_ordering                          kbo
% 2.76/1.00  --res_to_prop_solver                    active
% 2.76/1.00  --res_prop_simpl_new                    false
% 2.76/1.00  --res_prop_simpl_given                  true
% 2.76/1.00  --res_passive_queue_type                priority_queues
% 2.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.00  --res_passive_queues_freq               [15;5]
% 2.76/1.00  --res_forward_subs                      full
% 2.76/1.00  --res_backward_subs                     full
% 2.76/1.00  --res_forward_subs_resolution           true
% 2.76/1.00  --res_backward_subs_resolution          true
% 2.76/1.00  --res_orphan_elimination                true
% 2.76/1.00  --res_time_limit                        2.
% 2.76/1.00  --res_out_proof                         true
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Options
% 2.76/1.00  
% 2.76/1.00  --superposition_flag                    true
% 2.76/1.00  --sup_passive_queue_type                priority_queues
% 2.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.00  --demod_completeness_check              fast
% 2.76/1.00  --demod_use_ground                      true
% 2.76/1.00  --sup_to_prop_solver                    passive
% 2.76/1.00  --sup_prop_simpl_new                    true
% 2.76/1.00  --sup_prop_simpl_given                  true
% 2.76/1.00  --sup_fun_splitting                     false
% 2.76/1.00  --sup_smt_interval                      50000
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Simplification Setup
% 2.76/1.00  
% 2.76/1.00  --sup_indices_passive                   []
% 2.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_full_bw                           [BwDemod]
% 2.76/1.00  --sup_immed_triv                        [TrivRules]
% 2.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_immed_bw_main                     []
% 2.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.00  
% 2.76/1.00  ------ Combination Options
% 2.76/1.00  
% 2.76/1.00  --comb_res_mult                         3
% 2.76/1.00  --comb_sup_mult                         2
% 2.76/1.00  --comb_inst_mult                        10
% 2.76/1.00  
% 2.76/1.00  ------ Debug Options
% 2.76/1.00  
% 2.76/1.00  --dbg_backtrace                         false
% 2.76/1.00  --dbg_dump_prop_clauses                 false
% 2.76/1.00  --dbg_dump_prop_clauses_file            -
% 2.76/1.00  --dbg_out_stat                          false
% 2.76/1.00  ------ Parsing...
% 2.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/1.00  ------ Proving...
% 2.76/1.00  ------ Problem Properties 
% 2.76/1.00  
% 2.76/1.00  
% 2.76/1.00  clauses                                 21
% 2.76/1.00  conjectures                             2
% 2.76/1.00  EPR                                     1
% 2.76/1.00  Horn                                    16
% 2.76/1.00  unary                                   11
% 2.76/1.00  binary                                  4
% 2.76/1.00  lits                                    42
% 2.76/1.00  lits eq                                 17
% 2.76/1.00  fd_pure                                 0
% 2.76/1.00  fd_pseudo                               0
% 2.76/1.00  fd_cond                                 1
% 2.76/1.00  fd_pseudo_cond                          4
% 2.76/1.00  AC symbols                              0
% 2.76/1.00  
% 2.76/1.00  ------ Schedule dynamic 5 is on 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/1.00  
% 2.76/1.00  
% 2.76/1.00  ------ 
% 2.76/1.00  Current options:
% 2.76/1.00  ------ 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options
% 2.76/1.00  
% 2.76/1.00  --out_options                           all
% 2.76/1.00  --tptp_safe_out                         true
% 2.76/1.00  --problem_path                          ""
% 2.76/1.00  --include_path                          ""
% 2.76/1.00  --clausifier                            res/vclausify_rel
% 2.76/1.00  --clausifier_options                    --mode clausify
% 2.76/1.00  --stdin                                 false
% 2.76/1.00  --stats_out                             all
% 2.76/1.00  
% 2.76/1.00  ------ General Options
% 2.76/1.00  
% 2.76/1.00  --fof                                   false
% 2.76/1.00  --time_out_real                         305.
% 2.76/1.00  --time_out_virtual                      -1.
% 2.76/1.00  --symbol_type_check                     false
% 2.76/1.00  --clausify_out                          false
% 2.76/1.00  --sig_cnt_out                           false
% 2.76/1.00  --trig_cnt_out                          false
% 2.76/1.00  --trig_cnt_out_tolerance                1.
% 2.76/1.00  --trig_cnt_out_sk_spl                   false
% 2.76/1.00  --abstr_cl_out                          false
% 2.76/1.00  
% 2.76/1.00  ------ Global Options
% 2.76/1.00  
% 2.76/1.00  --schedule                              default
% 2.76/1.00  --add_important_lit                     false
% 2.76/1.00  --prop_solver_per_cl                    1000
% 2.76/1.00  --min_unsat_core                        false
% 2.76/1.00  --soft_assumptions                      false
% 2.76/1.00  --soft_lemma_size                       3
% 2.76/1.00  --prop_impl_unit_size                   0
% 2.76/1.00  --prop_impl_unit                        []
% 2.76/1.00  --share_sel_clauses                     true
% 2.76/1.00  --reset_solvers                         false
% 2.76/1.00  --bc_imp_inh                            [conj_cone]
% 2.76/1.00  --conj_cone_tolerance                   3.
% 2.76/1.00  --extra_neg_conj                        none
% 2.76/1.00  --large_theory_mode                     true
% 2.76/1.00  --prolific_symb_bound                   200
% 2.76/1.00  --lt_threshold                          2000
% 2.76/1.00  --clause_weak_htbl                      true
% 2.76/1.00  --gc_record_bc_elim                     false
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing Options
% 2.76/1.00  
% 2.76/1.00  --preprocessing_flag                    true
% 2.76/1.00  --time_out_prep_mult                    0.1
% 2.76/1.00  --splitting_mode                        input
% 2.76/1.00  --splitting_grd                         true
% 2.76/1.00  --splitting_cvd                         false
% 2.76/1.00  --splitting_cvd_svl                     false
% 2.76/1.00  --splitting_nvd                         32
% 2.76/1.00  --sub_typing                            true
% 2.76/1.00  --prep_gs_sim                           true
% 2.76/1.00  --prep_unflatten                        true
% 2.76/1.00  --prep_res_sim                          true
% 2.76/1.00  --prep_upred                            true
% 2.76/1.00  --prep_sem_filter                       exhaustive
% 2.76/1.00  --prep_sem_filter_out                   false
% 2.76/1.00  --pred_elim                             true
% 2.76/1.00  --res_sim_input                         true
% 2.76/1.00  --eq_ax_congr_red                       true
% 2.76/1.00  --pure_diseq_elim                       true
% 2.76/1.00  --brand_transform                       false
% 2.76/1.00  --non_eq_to_eq                          false
% 2.76/1.00  --prep_def_merge                        true
% 2.76/1.00  --prep_def_merge_prop_impl              false
% 2.76/1.00  --prep_def_merge_mbd                    true
% 2.76/1.00  --prep_def_merge_tr_red                 false
% 2.76/1.00  --prep_def_merge_tr_cl                  false
% 2.76/1.00  --smt_preprocessing                     true
% 2.76/1.00  --smt_ac_axioms                         fast
% 2.76/1.00  --preprocessed_out                      false
% 2.76/1.00  --preprocessed_stats                    false
% 2.76/1.00  
% 2.76/1.00  ------ Abstraction refinement Options
% 2.76/1.00  
% 2.76/1.00  --abstr_ref                             []
% 2.76/1.00  --abstr_ref_prep                        false
% 2.76/1.00  --abstr_ref_until_sat                   false
% 2.76/1.00  --abstr_ref_sig_restrict                funpre
% 2.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.00  --abstr_ref_under                       []
% 2.76/1.00  
% 2.76/1.00  ------ SAT Options
% 2.76/1.00  
% 2.76/1.00  --sat_mode                              false
% 2.76/1.00  --sat_fm_restart_options                ""
% 2.76/1.00  --sat_gr_def                            false
% 2.76/1.00  --sat_epr_types                         true
% 2.76/1.00  --sat_non_cyclic_types                  false
% 2.76/1.00  --sat_finite_models                     false
% 2.76/1.00  --sat_fm_lemmas                         false
% 2.76/1.00  --sat_fm_prep                           false
% 2.76/1.00  --sat_fm_uc_incr                        true
% 2.76/1.00  --sat_out_model                         small
% 2.76/1.00  --sat_out_clauses                       false
% 2.76/1.00  
% 2.76/1.00  ------ QBF Options
% 2.76/1.00  
% 2.76/1.00  --qbf_mode                              false
% 2.76/1.00  --qbf_elim_univ                         false
% 2.76/1.00  --qbf_dom_inst                          none
% 2.76/1.00  --qbf_dom_pre_inst                      false
% 2.76/1.00  --qbf_sk_in                             false
% 2.76/1.00  --qbf_pred_elim                         true
% 2.76/1.00  --qbf_split                             512
% 2.76/1.00  
% 2.76/1.00  ------ BMC1 Options
% 2.76/1.00  
% 2.76/1.00  --bmc1_incremental                      false
% 2.76/1.00  --bmc1_axioms                           reachable_all
% 2.76/1.00  --bmc1_min_bound                        0
% 2.76/1.00  --bmc1_max_bound                        -1
% 2.76/1.00  --bmc1_max_bound_default                -1
% 2.76/1.00  --bmc1_symbol_reachability              true
% 2.76/1.00  --bmc1_property_lemmas                  false
% 2.76/1.00  --bmc1_k_induction                      false
% 2.76/1.00  --bmc1_non_equiv_states                 false
% 2.76/1.00  --bmc1_deadlock                         false
% 2.76/1.00  --bmc1_ucm                              false
% 2.76/1.00  --bmc1_add_unsat_core                   none
% 2.76/1.00  --bmc1_unsat_core_children              false
% 2.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.00  --bmc1_out_stat                         full
% 2.76/1.00  --bmc1_ground_init                      false
% 2.76/1.00  --bmc1_pre_inst_next_state              false
% 2.76/1.00  --bmc1_pre_inst_state                   false
% 2.76/1.00  --bmc1_pre_inst_reach_state             false
% 2.76/1.00  --bmc1_out_unsat_core                   false
% 2.76/1.00  --bmc1_aig_witness_out                  false
% 2.76/1.00  --bmc1_verbose                          false
% 2.76/1.00  --bmc1_dump_clauses_tptp                false
% 2.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.00  --bmc1_dump_file                        -
% 2.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.00  --bmc1_ucm_extend_mode                  1
% 2.76/1.00  --bmc1_ucm_init_mode                    2
% 2.76/1.00  --bmc1_ucm_cone_mode                    none
% 2.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.00  --bmc1_ucm_relax_model                  4
% 2.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.00  --bmc1_ucm_layered_model                none
% 2.76/1.00  --bmc1_ucm_max_lemma_size               10
% 2.76/1.00  
% 2.76/1.00  ------ AIG Options
% 2.76/1.00  
% 2.76/1.00  --aig_mode                              false
% 2.76/1.00  
% 2.76/1.00  ------ Instantiation Options
% 2.76/1.00  
% 2.76/1.00  --instantiation_flag                    true
% 2.76/1.00  --inst_sos_flag                         false
% 2.76/1.00  --inst_sos_phase                        true
% 2.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel_side                     none
% 2.76/1.00  --inst_solver_per_active                1400
% 2.76/1.00  --inst_solver_calls_frac                1.
% 2.76/1.00  --inst_passive_queue_type               priority_queues
% 2.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.00  --inst_passive_queues_freq              [25;2]
% 2.76/1.00  --inst_dismatching                      true
% 2.76/1.00  --inst_eager_unprocessed_to_passive     true
% 2.76/1.00  --inst_prop_sim_given                   true
% 2.76/1.00  --inst_prop_sim_new                     false
% 2.76/1.00  --inst_subs_new                         false
% 2.76/1.00  --inst_eq_res_simp                      false
% 2.76/1.00  --inst_subs_given                       false
% 2.76/1.00  --inst_orphan_elimination               true
% 2.76/1.00  --inst_learning_loop_flag               true
% 2.76/1.00  --inst_learning_start                   3000
% 2.76/1.00  --inst_learning_factor                  2
% 2.76/1.00  --inst_start_prop_sim_after_learn       3
% 2.76/1.00  --inst_sel_renew                        solver
% 2.76/1.00  --inst_lit_activity_flag                true
% 2.76/1.00  --inst_restr_to_given                   false
% 2.76/1.00  --inst_activity_threshold               500
% 2.76/1.00  --inst_out_proof                        true
% 2.76/1.00  
% 2.76/1.00  ------ Resolution Options
% 2.76/1.00  
% 2.76/1.00  --resolution_flag                       false
% 2.76/1.00  --res_lit_sel                           adaptive
% 2.76/1.00  --res_lit_sel_side                      none
% 2.76/1.00  --res_ordering                          kbo
% 2.76/1.00  --res_to_prop_solver                    active
% 2.76/1.00  --res_prop_simpl_new                    false
% 2.76/1.00  --res_prop_simpl_given                  true
% 2.76/1.00  --res_passive_queue_type                priority_queues
% 2.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.00  --res_passive_queues_freq               [15;5]
% 2.76/1.00  --res_forward_subs                      full
% 2.76/1.00  --res_backward_subs                     full
% 2.76/1.00  --res_forward_subs_resolution           true
% 2.76/1.00  --res_backward_subs_resolution          true
% 2.76/1.00  --res_orphan_elimination                true
% 2.76/1.00  --res_time_limit                        2.
% 2.76/1.00  --res_out_proof                         true
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Options
% 2.76/1.00  
% 2.76/1.00  --superposition_flag                    true
% 2.76/1.00  --sup_passive_queue_type                priority_queues
% 2.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.00  --demod_completeness_check              fast
% 2.76/1.00  --demod_use_ground                      true
% 2.76/1.01  --sup_to_prop_solver                    passive
% 2.76/1.01  --sup_prop_simpl_new                    true
% 2.76/1.01  --sup_prop_simpl_given                  true
% 2.76/1.01  --sup_fun_splitting                     false
% 2.76/1.01  --sup_smt_interval                      50000
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Simplification Setup
% 2.76/1.01  
% 2.76/1.01  --sup_indices_passive                   []
% 2.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_full_bw                           [BwDemod]
% 2.76/1.01  --sup_immed_triv                        [TrivRules]
% 2.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_immed_bw_main                     []
% 2.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  
% 2.76/1.01  ------ Combination Options
% 2.76/1.01  
% 2.76/1.01  --comb_res_mult                         3
% 2.76/1.01  --comb_sup_mult                         2
% 2.76/1.01  --comb_inst_mult                        10
% 2.76/1.01  
% 2.76/1.01  ------ Debug Options
% 2.76/1.01  
% 2.76/1.01  --dbg_backtrace                         false
% 2.76/1.01  --dbg_dump_prop_clauses                 false
% 2.76/1.01  --dbg_dump_prop_clauses_file            -
% 2.76/1.01  --dbg_out_stat                          false
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  ------ Proving...
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  % SZS status Theorem for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01   Resolution empty clause
% 2.76/1.01  
% 2.76/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  fof(f6,axiom,(
% 2.76/1.01    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f10,plain,(
% 2.76/1.01    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.76/1.01    inference(ennf_transformation,[],[f6])).
% 2.76/1.01  
% 2.76/1.01  fof(f22,plain,(
% 2.76/1.01    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f23,plain,(
% 2.76/1.01    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f22])).
% 2.76/1.01  
% 2.76/1.01  fof(f43,plain,(
% 2.76/1.01    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 2.76/1.01    inference(cnf_transformation,[],[f23])).
% 2.76/1.01  
% 2.76/1.01  fof(f5,axiom,(
% 2.76/1.01    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f9,plain,(
% 2.76/1.01    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.76/1.01    inference(ennf_transformation,[],[f5])).
% 2.76/1.01  
% 2.76/1.01  fof(f20,plain,(
% 2.76/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f21,plain,(
% 2.76/1.01    ! [X0,X1] : (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)))),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f20])).
% 2.76/1.01  
% 2.76/1.01  fof(f39,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0) )),
% 2.76/1.01    inference(cnf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f7,conjecture,(
% 2.76/1.01    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f8,negated_conjecture,(
% 2.76/1.01    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.76/1.01    inference(negated_conjecture,[],[f7])).
% 2.76/1.01  
% 2.76/1.01  fof(f11,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 2.76/1.01    inference(ennf_transformation,[],[f8])).
% 2.76/1.01  
% 2.76/1.01  fof(f12,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.76/1.01    inference(flattening,[],[f11])).
% 2.76/1.01  
% 2.76/1.01  fof(f24,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f25,plain,(
% 2.76/1.01    k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f24])).
% 2.76/1.01  
% 2.76/1.01  fof(f45,plain,(
% 2.76/1.01    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f25])).
% 2.76/1.01  
% 2.76/1.01  fof(f37,plain,(
% 2.76/1.01    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f38,plain,(
% 2.76/1.01    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f41,plain,(
% 2.76/1.01    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f23])).
% 2.76/1.01  
% 2.76/1.01  fof(f42,plain,(
% 2.76/1.01    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f23])).
% 2.76/1.01  
% 2.76/1.01  fof(f1,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f13,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/1.01    inference(nnf_transformation,[],[f1])).
% 2.76/1.01  
% 2.76/1.01  fof(f14,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/1.01    inference(flattening,[],[f13])).
% 2.76/1.01  
% 2.76/1.01  fof(f15,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/1.01    inference(rectify,[],[f14])).
% 2.76/1.01  
% 2.76/1.01  fof(f16,plain,(
% 2.76/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f17,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.76/1.01  
% 2.76/1.01  fof(f29,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f17])).
% 2.76/1.01  
% 2.76/1.01  fof(f3,axiom,(
% 2.76/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f18,plain,(
% 2.76/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.76/1.01    inference(nnf_transformation,[],[f3])).
% 2.76/1.01  
% 2.76/1.01  fof(f19,plain,(
% 2.76/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.76/1.01    inference(flattening,[],[f18])).
% 2.76/1.01  
% 2.76/1.01  fof(f35,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.76/1.01    inference(cnf_transformation,[],[f19])).
% 2.76/1.01  
% 2.76/1.01  fof(f50,plain,(
% 2.76/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.76/1.01    inference(equality_resolution,[],[f35])).
% 2.76/1.01  
% 2.76/1.01  fof(f4,axiom,(
% 2.76/1.01    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f36,plain,(
% 2.76/1.01    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.76/1.01    inference(cnf_transformation,[],[f4])).
% 2.76/1.01  
% 2.76/1.01  fof(f2,axiom,(
% 2.76/1.01    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f32,plain,(
% 2.76/1.01    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 2.76/1.01    inference(cnf_transformation,[],[f2])).
% 2.76/1.01  
% 2.76/1.01  fof(f40,plain,(
% 2.76/1.01    ( ! [X0,X3,X1] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f46,plain,(
% 2.76/1.01    k1_xboole_0 != sK3),
% 2.76/1.01    inference(cnf_transformation,[],[f25])).
% 2.76/1.01  
% 2.76/1.01  fof(f33,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f19])).
% 2.76/1.01  
% 2.76/1.01  fof(f34,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.76/1.01    inference(cnf_transformation,[],[f19])).
% 2.76/1.01  
% 2.76/1.01  fof(f51,plain,(
% 2.76/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.76/1.01    inference(equality_resolution,[],[f34])).
% 2.76/1.01  
% 2.76/1.01  fof(f44,plain,(
% 2.76/1.01    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f23])).
% 2.76/1.01  
% 2.76/1.01  cnf(c_16,plain,
% 2.76/1.01      ( k1_relat_1(sK2(X0)) = X0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_12,plain,
% 2.76/1.01      ( k1_relat_1(sK1(X0,X1)) = X0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_20,negated_conjecture,
% 2.76/1.01      ( ~ v1_relat_1(X0)
% 2.76/1.01      | ~ v1_relat_1(X1)
% 2.76/1.01      | ~ v1_funct_1(X0)
% 2.76/1.01      | ~ v1_funct_1(X1)
% 2.76/1.01      | X1 = X0
% 2.76/1.01      | k1_relat_1(X0) != sK3
% 2.76/1.01      | k1_relat_1(X1) != sK3 ),
% 2.76/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_434,plain,
% 2.76/1.01      ( X0 = X1
% 2.76/1.01      | k1_relat_1(X0) != sK3
% 2.76/1.01      | k1_relat_1(X1) != sK3
% 2.76/1.01      | v1_relat_1(X1) != iProver_top
% 2.76/1.01      | v1_relat_1(X0) != iProver_top
% 2.76/1.01      | v1_funct_1(X1) != iProver_top
% 2.76/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_845,plain,
% 2.76/1.01      ( sK1(X0,X1) = X2
% 2.76/1.01      | k1_relat_1(X2) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X2) != iProver_top
% 2.76/1.01      | v1_relat_1(sK1(X0,X1)) != iProver_top
% 2.76/1.01      | v1_funct_1(X2) != iProver_top
% 2.76/1.01      | v1_funct_1(sK1(X0,X1)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_12,c_434]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_14,plain,
% 2.76/1.01      ( v1_relat_1(sK1(X0,X1)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_34,plain,
% 2.76/1.01      ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_13,plain,
% 2.76/1.01      ( v1_funct_1(sK1(X0,X1)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_37,plain,
% 2.76/1.01      ( v1_funct_1(sK1(X0,X1)) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_989,plain,
% 2.76/1.01      ( v1_funct_1(X2) != iProver_top
% 2.76/1.01      | sK1(X0,X1) = X2
% 2.76/1.01      | k1_relat_1(X2) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X2) != iProver_top ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_845,c_34,c_37]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_990,plain,
% 2.76/1.01      ( sK1(X0,X1) = X2
% 2.76/1.01      | k1_relat_1(X2) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X2) != iProver_top
% 2.76/1.01      | v1_funct_1(X2) != iProver_top ),
% 2.76/1.01      inference(renaming,[status(thm)],[c_989]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1001,plain,
% 2.76/1.01      ( sK1(X0,X1) = sK2(X2)
% 2.76/1.01      | sK3 != X2
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(sK2(X2)) != iProver_top
% 2.76/1.01      | v1_funct_1(sK2(X2)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_16,c_990]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_602,plain,
% 2.76/1.01      ( sK2(X0) = X1
% 2.76/1.01      | k1_relat_1(X1) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X1) != iProver_top
% 2.76/1.01      | v1_relat_1(sK2(X0)) != iProver_top
% 2.76/1.01      | v1_funct_1(X1) != iProver_top
% 2.76/1.01      | v1_funct_1(sK2(X0)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_16,c_434]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_18,plain,
% 2.76/1.01      ( v1_relat_1(sK2(X0)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_24,plain,
% 2.76/1.01      ( v1_relat_1(sK2(X0)) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_17,plain,
% 2.76/1.01      ( v1_funct_1(sK2(X0)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_27,plain,
% 2.76/1.01      ( v1_funct_1(sK2(X0)) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_755,plain,
% 2.76/1.01      ( v1_funct_1(X1) != iProver_top
% 2.76/1.01      | sK2(X0) = X1
% 2.76/1.01      | k1_relat_1(X1) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_602,c_24,c_27]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_756,plain,
% 2.76/1.01      ( sK2(X0) = X1
% 2.76/1.01      | k1_relat_1(X1) != sK3
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | v1_relat_1(X1) != iProver_top
% 2.76/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.76/1.01      inference(renaming,[status(thm)],[c_755]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_844,plain,
% 2.76/1.01      ( sK1(X0,X1) = sK2(X2)
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | sK3 != X2
% 2.76/1.01      | v1_relat_1(sK1(X0,X1)) != iProver_top
% 2.76/1.01      | v1_funct_1(sK1(X0,X1)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_12,c_756]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_870,plain,
% 2.76/1.01      ( ~ v1_relat_1(sK1(X0,X1))
% 2.76/1.01      | ~ v1_funct_1(sK1(X0,X1))
% 2.76/1.01      | sK1(X0,X1) = sK2(X2)
% 2.76/1.01      | sK3 != X0
% 2.76/1.01      | sK3 != X2 ),
% 2.76/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_844]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1094,plain,
% 2.76/1.01      ( sK1(X0,X1) = sK2(X2) | sK3 != X2 | sK3 != X0 ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_1001,c_14,c_13,c_870]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1095,plain,
% 2.76/1.01      ( sK1(X0,X1) = sK2(X2) | sK3 != X0 | sK3 != X2 ),
% 2.76/1.01      inference(renaming,[status(thm)],[c_1094]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1100,plain,
% 2.76/1.01      ( sK1(sK3,X0) = sK2(X1) | sK3 != X1 ),
% 2.76/1.01      inference(equality_resolution,[status(thm)],[c_1095]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1208,plain,
% 2.76/1.01      ( sK1(sK3,X0) = sK2(sK3) ),
% 2.76/1.01      inference(equality_resolution,[status(thm)],[c_1100]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2,plain,
% 2.76/1.01      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.76/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.76/1.01      | k4_xboole_0(X0,X1) = X2 ),
% 2.76/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_445,plain,
% 2.76/1.01      ( k4_xboole_0(X0,X1) = X2
% 2.76/1.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 2.76/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_7,plain,
% 2.76/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_10,plain,
% 2.76/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_441,plain,
% 2.76/1.01      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1435,plain,
% 2.76/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_7,c_441]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2203,plain,
% 2.76/1.01      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 2.76/1.01      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_445,c_1435]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_6,plain,
% 2.76/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2213,plain,
% 2.76/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.76/1.01      inference(demodulation,[status(thm)],[c_2203,c_6]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_11,plain,
% 2.76/1.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK1(X1,X2),X0) = X2 ),
% 2.76/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_440,plain,
% 2.76/1.01      ( k1_funct_1(sK1(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2393,plain,
% 2.76/1.01      ( k1_funct_1(sK1(X0,X1),sK0(k1_xboole_0,X2,X0)) = X1 | k1_xboole_0 = X0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_2213,c_440]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2909,plain,
% 2.76/1.01      ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = X1 | sK3 = k1_xboole_0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1208,c_2393]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_19,negated_conjecture,
% 2.76/1.01      ( k1_xboole_0 != sK3 ),
% 2.76/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_9,plain,
% 2.76/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.76/1.01      | k1_xboole_0 = X1
% 2.76/1.01      | k1_xboole_0 = X0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_47,plain,
% 2.76/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.76/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.76/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_8,plain,
% 2.76/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_48,plain,
% 2.76/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.76/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_174,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_596,plain,
% 2.76/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.76/1.01      inference(instantiation,[status(thm)],[c_174]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_597,plain,
% 2.76/1.01      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.76/1.01      inference(instantiation,[status(thm)],[c_596]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3064,plain,
% 2.76/1.01      ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = X1 ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_2909,c_19,c_47,c_48,c_597]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3111,plain,
% 2.76/1.01      ( k1_relat_1(k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3))) = X1 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_3064,c_12]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3114,plain,
% 2.76/1.01      ( k1_funct_1(sK2(sK3),sK0(k1_xboole_0,X0,sK3)) = k1_xboole_0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_3064,c_8]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3709,plain,
% 2.76/1.01      ( k1_relat_1(k1_xboole_0) = X0 ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_3111,c_3114]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3751,plain,
% 2.76/1.01      ( sK2(X0) = k1_relat_1(k1_xboole_0) | sK3 != X1 | sK3 != X0 ),
% 2.76/1.01      inference(demodulation,[status(thm)],[c_3709,c_1095]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_15,plain,
% 2.76/1.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK2(X1),X0) = k1_xboole_0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_437,plain,
% 2.76/1.01      ( k1_funct_1(sK2(X0),X1) = k1_xboole_0
% 2.76/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2394,plain,
% 2.76/1.01      ( k1_funct_1(sK2(X0),sK0(k1_xboole_0,X1,X0)) = k1_xboole_0
% 2.76/1.01      | k1_xboole_0 = X0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_2213,c_437]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_3085,plain,
% 2.76/1.01      ( sK3 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_3064,c_2394]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4506,plain,
% 2.76/1.01      ( sK3 != X0 ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_3751,c_19,c_47,c_48,c_596,c_597,c_3085]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4510,plain,
% 2.76/1.01      ( $false ),
% 2.76/1.01      inference(equality_resolution,[status(thm)],[c_4506]) ).
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  ------                               Statistics
% 2.76/1.01  
% 2.76/1.01  ------ General
% 2.76/1.01  
% 2.76/1.01  abstr_ref_over_cycles:                  0
% 2.76/1.01  abstr_ref_under_cycles:                 0
% 2.76/1.01  gc_basic_clause_elim:                   0
% 2.76/1.01  forced_gc_time:                         0
% 2.76/1.01  parsing_time:                           0.022
% 2.76/1.01  unif_index_cands_time:                  0.
% 2.76/1.01  unif_index_add_time:                    0.
% 2.76/1.01  orderings_time:                         0.
% 2.76/1.01  out_proof_time:                         0.008
% 2.76/1.01  total_time:                             0.278
% 2.76/1.01  num_of_symbols:                         43
% 2.76/1.01  num_of_terms:                           5013
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing
% 2.76/1.01  
% 2.76/1.01  num_of_splits:                          0
% 2.76/1.01  num_of_split_atoms:                     0
% 2.76/1.01  num_of_reused_defs:                     0
% 2.76/1.01  num_eq_ax_congr_red:                    16
% 2.76/1.01  num_of_sem_filtered_clauses:            1
% 2.76/1.01  num_of_subtypes:                        0
% 2.76/1.01  monotx_restored_types:                  0
% 2.76/1.01  sat_num_of_epr_types:                   0
% 2.76/1.01  sat_num_of_non_cyclic_types:            0
% 2.76/1.01  sat_guarded_non_collapsed_types:        0
% 2.76/1.01  num_pure_diseq_elim:                    0
% 2.76/1.01  simp_replaced_by:                       0
% 2.76/1.01  res_preprocessed:                       82
% 2.76/1.01  prep_upred:                             0
% 2.76/1.01  prep_unflattend:                        0
% 2.76/1.01  smt_new_axioms:                         0
% 2.76/1.01  pred_elim_cands:                        3
% 2.76/1.01  pred_elim:                              0
% 2.76/1.01  pred_elim_cl:                           0
% 2.76/1.01  pred_elim_cycles:                       1
% 2.76/1.01  merged_defs:                            0
% 2.76/1.01  merged_defs_ncl:                        0
% 2.76/1.01  bin_hyper_res:                          0
% 2.76/1.01  prep_cycles:                            3
% 2.76/1.01  pred_elim_time:                         0.
% 2.76/1.01  splitting_time:                         0.
% 2.76/1.01  sem_filter_time:                        0.
% 2.76/1.01  monotx_time:                            0.001
% 2.76/1.01  subtype_inf_time:                       0.
% 2.76/1.01  
% 2.76/1.01  ------ Problem properties
% 2.76/1.01  
% 2.76/1.01  clauses:                                21
% 2.76/1.01  conjectures:                            2
% 2.76/1.01  epr:                                    1
% 2.76/1.01  horn:                                   16
% 2.76/1.01  ground:                                 1
% 2.76/1.01  unary:                                  11
% 2.76/1.01  binary:                                 4
% 2.76/1.01  lits:                                   42
% 2.76/1.01  lits_eq:                                17
% 2.76/1.01  fd_pure:                                0
% 2.76/1.01  fd_pseudo:                              0
% 2.76/1.01  fd_cond:                                1
% 2.76/1.01  fd_pseudo_cond:                         4
% 2.76/1.01  ac_symbols:                             0
% 2.76/1.01  
% 2.76/1.01  ------ Propositional Solver
% 2.76/1.01  
% 2.76/1.01  prop_solver_calls:                      23
% 2.76/1.01  prop_fast_solver_calls:                 488
% 2.76/1.01  smt_solver_calls:                       0
% 2.76/1.01  smt_fast_solver_calls:                  0
% 2.76/1.01  prop_num_of_clauses:                    1570
% 2.76/1.01  prop_preprocess_simplified:             4503
% 2.76/1.01  prop_fo_subsumed:                       13
% 2.76/1.01  prop_solver_time:                       0.
% 2.76/1.01  smt_solver_time:                        0.
% 2.76/1.01  smt_fast_solver_time:                   0.
% 2.76/1.01  prop_fast_solver_time:                  0.
% 2.76/1.01  prop_unsat_core_time:                   0.
% 2.76/1.01  
% 2.76/1.01  ------ QBF
% 2.76/1.01  
% 2.76/1.01  qbf_q_res:                              0
% 2.76/1.01  qbf_num_tautologies:                    0
% 2.76/1.01  qbf_prep_cycles:                        0
% 2.76/1.01  
% 2.76/1.01  ------ BMC1
% 2.76/1.01  
% 2.76/1.01  bmc1_current_bound:                     -1
% 2.76/1.01  bmc1_last_solved_bound:                 -1
% 2.76/1.01  bmc1_unsat_core_size:                   -1
% 2.76/1.01  bmc1_unsat_core_parents_size:           -1
% 2.76/1.01  bmc1_merge_next_fun:                    0
% 2.76/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.76/1.01  
% 2.76/1.01  ------ Instantiation
% 2.76/1.01  
% 2.76/1.01  inst_num_of_clauses:                    493
% 2.76/1.01  inst_num_in_passive:                    64
% 2.76/1.01  inst_num_in_active:                     229
% 2.76/1.01  inst_num_in_unprocessed:                200
% 2.76/1.01  inst_num_of_loops:                      250
% 2.76/1.01  inst_num_of_learning_restarts:          0
% 2.76/1.01  inst_num_moves_active_passive:          19
% 2.76/1.01  inst_lit_activity:                      0
% 2.76/1.01  inst_lit_activity_moves:                0
% 2.76/1.01  inst_num_tautologies:                   0
% 2.76/1.01  inst_num_prop_implied:                  0
% 2.76/1.01  inst_num_existing_simplified:           0
% 2.76/1.01  inst_num_eq_res_simplified:             0
% 2.76/1.01  inst_num_child_elim:                    0
% 2.76/1.01  inst_num_of_dismatching_blockings:      84
% 2.76/1.01  inst_num_of_non_proper_insts:           433
% 2.76/1.01  inst_num_of_duplicates:                 0
% 2.76/1.01  inst_inst_num_from_inst_to_res:         0
% 2.76/1.01  inst_dismatching_checking_time:         0.
% 2.76/1.01  
% 2.76/1.01  ------ Resolution
% 2.76/1.01  
% 2.76/1.01  res_num_of_clauses:                     0
% 2.76/1.01  res_num_in_passive:                     0
% 2.76/1.01  res_num_in_active:                      0
% 2.76/1.01  res_num_of_loops:                       85
% 2.76/1.01  res_forward_subset_subsumed:            22
% 2.76/1.01  res_backward_subset_subsumed:           0
% 2.76/1.01  res_forward_subsumed:                   0
% 2.76/1.01  res_backward_subsumed:                  0
% 2.76/1.01  res_forward_subsumption_resolution:     0
% 2.76/1.01  res_backward_subsumption_resolution:    0
% 2.76/1.01  res_clause_to_clause_subsumption:       981
% 2.76/1.01  res_orphan_elimination:                 0
% 2.76/1.01  res_tautology_del:                      17
% 2.76/1.01  res_num_eq_res_simplified:              0
% 2.76/1.01  res_num_sel_changes:                    0
% 2.76/1.01  res_moves_from_active_to_pass:          0
% 2.76/1.01  
% 2.76/1.01  ------ Superposition
% 2.76/1.01  
% 2.76/1.01  sup_time_total:                         0.
% 2.76/1.01  sup_time_generating:                    0.
% 2.76/1.01  sup_time_sim_full:                      0.
% 2.76/1.01  sup_time_sim_immed:                     0.
% 2.76/1.01  
% 2.76/1.01  sup_num_of_clauses:                     87
% 2.76/1.01  sup_num_in_active:                      8
% 2.76/1.01  sup_num_in_passive:                     79
% 2.76/1.01  sup_num_of_loops:                       48
% 2.76/1.01  sup_fw_superposition:                   46
% 2.76/1.01  sup_bw_superposition:                   104
% 2.76/1.01  sup_immediate_simplified:               100
% 2.76/1.01  sup_given_eliminated:                   4
% 2.76/1.01  comparisons_done:                       0
% 2.76/1.01  comparisons_avoided:                    1
% 2.76/1.01  
% 2.76/1.01  ------ Simplifications
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  sim_fw_subset_subsumed:                 16
% 2.76/1.01  sim_bw_subset_subsumed:                 5
% 2.76/1.01  sim_fw_subsumed:                        28
% 2.76/1.01  sim_bw_subsumed:                        14
% 2.76/1.01  sim_fw_subsumption_res:                 10
% 2.76/1.01  sim_bw_subsumption_res:                 5
% 2.76/1.01  sim_tautology_del:                      5
% 2.76/1.01  sim_eq_tautology_del:                   9
% 2.76/1.01  sim_eq_res_simp:                        3
% 2.76/1.01  sim_fw_demodulated:                     16
% 2.76/1.01  sim_bw_demodulated:                     113
% 2.76/1.01  sim_light_normalised:                   24
% 2.76/1.01  sim_joinable_taut:                      0
% 2.76/1.01  sim_joinable_simp:                      0
% 2.76/1.01  sim_ac_normalised:                      0
% 2.76/1.01  sim_smt_subsumption:                    0
% 2.76/1.01  
%------------------------------------------------------------------------------
