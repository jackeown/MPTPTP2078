%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:25 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   98 (1488 expanded)
%              Number of clauses        :   55 ( 493 expanded)
%              Number of leaves         :   13 ( 374 expanded)
%              Depth                    :   25
%              Number of atoms          :  341 (7282 expanded)
%              Number of equality atoms :  211 (3765 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

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
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f22])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

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
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f20])).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f10])).

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
   => ( k1_xboole_0 != sK5
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK5
              | k1_relat_1(X1) != sK5
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_xboole_0 != sK5
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK5
            | k1_relat_1(X1) != sK5
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f24])).

fof(f42,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK5
      | k1_relat_1(X1) != sK5
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f27])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_390,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_797,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_390])).

cnf(c_11,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_31,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_34,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_982,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_31,c_34])).

cnf(c_983,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_982])).

cnf(c_994,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0
    | v1_relat_1(sK4(X2)) != iProver_top
    | v1_funct_1(sK4(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_983])).

cnf(c_536,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_390])).

cnf(c_15,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_541,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_21,c_24])).

cnf(c_542,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_796,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2
    | v1_relat_1(sK3(X0,X1)) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_542])).

cnf(c_822,plain,
    ( ~ v1_relat_1(sK3(X0,X1))
    | ~ v1_funct_1(sK3(X0,X1))
    | sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_796])).

cnf(c_1092,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_994,c_11,c_10,c_822])).

cnf(c_1093,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(renaming,[status(thm)],[c_1092])).

cnf(c_1098,plain,
    ( sK3(sK5,X0) = sK4(X1)
    | sK5 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1093])).

cnf(c_1151,plain,
    ( sK3(sK5,X0) = sK4(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1098])).

cnf(c_5,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_399,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_398,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1871,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_399,c_398])).

cnf(c_2530,plain,
    ( k1_relat_1(sK3(X0,X1)) = X2
    | r2_hidden(sK0(sK3(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK0(sK3(X0,X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1871])).

cnf(c_2624,plain,
    ( X0 = X1
    | r2_hidden(sK0(sK3(X1,X2),X0),X1) = iProver_top
    | r2_hidden(sK0(sK3(X1,X2),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2530,c_9])).

cnf(c_4245,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK3(sK5,X1),X0),X0) = iProver_top
    | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_2624])).

cnf(c_4432,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK4(sK5),X0),X0) = iProver_top
    | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4245,c_1151])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_401,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1361,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_401])).

cnf(c_4925,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4432,c_1361])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_57,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_158,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_530,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_531,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_5476,plain,
    ( r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4925,c_16,c_56,c_57,c_531])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_396,plain,
    ( k1_funct_1(sK3(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5485,plain,
    ( k1_funct_1(sK3(sK5,X0),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_5476,c_396])).

cnf(c_5504,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5485,c_1151])).

cnf(c_5611,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_5504,c_5504])).

cnf(c_6045,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_5611,c_16])).

cnf(c_6056,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6045,c_5611])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.79/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/1.00  
% 2.79/1.00  ------  iProver source info
% 2.79/1.00  
% 2.79/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.79/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/1.00  git: non_committed_changes: false
% 2.79/1.00  git: last_make_outside_of_git: false
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     num_symb
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       true
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  ------ Parsing...
% 2.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/1.00  ------ Proving...
% 2.79/1.00  ------ Problem Properties 
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  clauses                                 18
% 2.79/1.00  conjectures                             2
% 2.79/1.00  EPR                                     1
% 2.79/1.00  Horn                                    16
% 2.79/1.00  unary                                   10
% 2.79/1.00  binary                                  4
% 2.79/1.00  lits                                    34
% 2.79/1.00  lits eq                                 15
% 2.79/1.00  fd_pure                                 0
% 2.79/1.00  fd_pseudo                               0
% 2.79/1.00  fd_cond                                 1
% 2.79/1.00  fd_pseudo_cond                          3
% 2.79/1.00  AC symbols                              0
% 2.79/1.00  
% 2.79/1.00  ------ Schedule dynamic 5 is on 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  Current options:
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     none
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       false
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ Proving...
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS status Theorem for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00   Resolution empty clause
% 2.79/1.00  
% 2.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  fof(f5,axiom,(
% 2.79/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f9,plain,(
% 2.79/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.79/1.00    inference(ennf_transformation,[],[f5])).
% 2.79/1.00  
% 2.79/1.00  fof(f22,plain,(
% 2.79/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f23,plain,(
% 2.79/1.00    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f22])).
% 2.79/1.00  
% 2.79/1.00  fof(f40,plain,(
% 2.79/1.00    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 2.79/1.00    inference(cnf_transformation,[],[f23])).
% 2.79/1.00  
% 2.79/1.00  fof(f4,axiom,(
% 2.79/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f8,plain,(
% 2.79/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.79/1.00    inference(ennf_transformation,[],[f4])).
% 2.79/1.00  
% 2.79/1.00  fof(f20,plain,(
% 2.79/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f21,plain,(
% 2.79/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f20])).
% 2.79/1.00  
% 2.79/1.00  fof(f36,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f6,conjecture,(
% 2.79/1.00    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f7,negated_conjecture,(
% 2.79/1.00    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.79/1.00    inference(negated_conjecture,[],[f6])).
% 2.79/1.00  
% 2.79/1.00  fof(f10,plain,(
% 2.79/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 2.79/1.00    inference(ennf_transformation,[],[f7])).
% 2.79/1.00  
% 2.79/1.00  fof(f11,plain,(
% 2.79/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.79/1.00    inference(flattening,[],[f10])).
% 2.79/1.00  
% 2.79/1.00  fof(f24,plain,(
% 2.79/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f25,plain,(
% 2.79/1.00    k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f24])).
% 2.79/1.00  
% 2.79/1.00  fof(f42,plain,(
% 2.79/1.00    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f25])).
% 2.79/1.00  
% 2.79/1.00  fof(f34,plain,(
% 2.79/1.00    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f35,plain,(
% 2.79/1.00    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f38,plain,(
% 2.79/1.00    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f23])).
% 2.79/1.00  
% 2.79/1.00  fof(f39,plain,(
% 2.79/1.00    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f23])).
% 2.79/1.00  
% 2.79/1.00  fof(f3,axiom,(
% 2.79/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f14,plain,(
% 2.79/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.79/1.00    inference(nnf_transformation,[],[f3])).
% 2.79/1.00  
% 2.79/1.00  fof(f15,plain,(
% 2.79/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.79/1.00    inference(rectify,[],[f14])).
% 2.79/1.00  
% 2.79/1.00  fof(f18,plain,(
% 2.79/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f17,plain,(
% 2.79/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f16,plain,(
% 2.79/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f19,plain,(
% 2.79/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 2.79/1.00  
% 2.79/1.00  fof(f32,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f19])).
% 2.79/1.00  
% 2.79/1.00  fof(f31,plain,(
% 2.79/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.79/1.00    inference(cnf_transformation,[],[f19])).
% 2.79/1.00  
% 2.79/1.00  fof(f46,plain,(
% 2.79/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.79/1.00    inference(equality_resolution,[],[f31])).
% 2.79/1.00  
% 2.79/1.00  fof(f1,axiom,(
% 2.79/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f12,plain,(
% 2.79/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/1.00    inference(nnf_transformation,[],[f1])).
% 2.79/1.00  
% 2.79/1.00  fof(f13,plain,(
% 2.79/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/1.00    inference(flattening,[],[f12])).
% 2.79/1.00  
% 2.79/1.00  fof(f28,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.79/1.00    inference(cnf_transformation,[],[f13])).
% 2.79/1.00  
% 2.79/1.00  fof(f44,plain,(
% 2.79/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.79/1.00    inference(equality_resolution,[],[f28])).
% 2.79/1.00  
% 2.79/1.00  fof(f2,axiom,(
% 2.79/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f29,plain,(
% 2.79/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f2])).
% 2.79/1.00  
% 2.79/1.00  fof(f43,plain,(
% 2.79/1.00    k1_xboole_0 != sK5),
% 2.79/1.00    inference(cnf_transformation,[],[f25])).
% 2.79/1.00  
% 2.79/1.00  fof(f26,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.79/1.00    inference(cnf_transformation,[],[f13])).
% 2.79/1.00  
% 2.79/1.00  fof(f27,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.79/1.00    inference(cnf_transformation,[],[f13])).
% 2.79/1.00  
% 2.79/1.00  fof(f45,plain,(
% 2.79/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.79/1.00    inference(equality_resolution,[],[f27])).
% 2.79/1.00  
% 2.79/1.00  fof(f37,plain,(
% 2.79/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  cnf(c_13,plain,
% 2.79/1.00      ( k1_relat_1(sK4(X0)) = X0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_9,plain,
% 2.79/1.00      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_17,negated_conjecture,
% 2.79/1.00      ( ~ v1_relat_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X1)
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_funct_1(X1)
% 2.79/1.00      | X1 = X0
% 2.79/1.00      | k1_relat_1(X0) != sK5
% 2.79/1.00      | k1_relat_1(X1) != sK5 ),
% 2.79/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_390,plain,
% 2.79/1.00      ( X0 = X1
% 2.79/1.00      | k1_relat_1(X0) != sK5
% 2.79/1.00      | k1_relat_1(X1) != sK5
% 2.79/1.00      | v1_relat_1(X1) != iProver_top
% 2.79/1.00      | v1_relat_1(X0) != iProver_top
% 2.79/1.00      | v1_funct_1(X1) != iProver_top
% 2.79/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_797,plain,
% 2.79/1.00      ( sK3(X0,X1) = X2
% 2.79/1.00      | k1_relat_1(X2) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X2) != iProver_top
% 2.79/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top
% 2.79/1.00      | v1_funct_1(X2) != iProver_top
% 2.79/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_9,c_390]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_11,plain,
% 2.79/1.00      ( v1_relat_1(sK3(X0,X1)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_31,plain,
% 2.79/1.00      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_10,plain,
% 2.79/1.00      ( v1_funct_1(sK3(X0,X1)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_34,plain,
% 2.79/1.00      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_982,plain,
% 2.79/1.00      ( v1_funct_1(X2) != iProver_top
% 2.79/1.00      | sK3(X0,X1) = X2
% 2.79/1.00      | k1_relat_1(X2) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_797,c_31,c_34]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_983,plain,
% 2.79/1.00      ( sK3(X0,X1) = X2
% 2.79/1.00      | k1_relat_1(X2) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X2) != iProver_top
% 2.79/1.00      | v1_funct_1(X2) != iProver_top ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_982]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_994,plain,
% 2.79/1.00      ( sK3(X0,X1) = sK4(X2)
% 2.79/1.00      | sK5 != X2
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(sK4(X2)) != iProver_top
% 2.79/1.00      | v1_funct_1(sK4(X2)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_13,c_983]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_536,plain,
% 2.79/1.00      ( sK4(X0) = X1
% 2.79/1.00      | k1_relat_1(X1) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X1) != iProver_top
% 2.79/1.00      | v1_relat_1(sK4(X0)) != iProver_top
% 2.79/1.00      | v1_funct_1(X1) != iProver_top
% 2.79/1.00      | v1_funct_1(sK4(X0)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_13,c_390]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_15,plain,
% 2.79/1.00      ( v1_relat_1(sK4(X0)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_21,plain,
% 2.79/1.00      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_14,plain,
% 2.79/1.00      ( v1_funct_1(sK4(X0)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_24,plain,
% 2.79/1.00      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_541,plain,
% 2.79/1.00      ( v1_funct_1(X1) != iProver_top
% 2.79/1.00      | sK4(X0) = X1
% 2.79/1.00      | k1_relat_1(X1) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_536,c_21,c_24]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_542,plain,
% 2.79/1.00      ( sK4(X0) = X1
% 2.79/1.00      | k1_relat_1(X1) != sK5
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | v1_relat_1(X1) != iProver_top
% 2.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_541]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_796,plain,
% 2.79/1.00      ( sK3(X0,X1) = sK4(X2)
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | sK5 != X2
% 2.79/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top
% 2.79/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_9,c_542]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_822,plain,
% 2.79/1.00      ( ~ v1_relat_1(sK3(X0,X1))
% 2.79/1.00      | ~ v1_funct_1(sK3(X0,X1))
% 2.79/1.00      | sK3(X0,X1) = sK4(X2)
% 2.79/1.00      | sK5 != X0
% 2.79/1.00      | sK5 != X2 ),
% 2.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_796]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1092,plain,
% 2.79/1.00      ( sK3(X0,X1) = sK4(X2) | sK5 != X2 | sK5 != X0 ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_994,c_11,c_10,c_822]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1093,plain,
% 2.79/1.00      ( sK3(X0,X1) = sK4(X2) | sK5 != X0 | sK5 != X2 ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_1092]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1098,plain,
% 2.79/1.00      ( sK3(sK5,X0) = sK4(X1) | sK5 != X1 ),
% 2.79/1.00      inference(equality_resolution,[status(thm)],[c_1093]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1151,plain,
% 2.79/1.00      ( sK3(sK5,X0) = sK4(sK5) ),
% 2.79/1.00      inference(equality_resolution,[status(thm)],[c_1098]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5,plain,
% 2.79/1.00      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 2.79/1.00      | r2_hidden(sK0(X0,X1),X1)
% 2.79/1.00      | k1_relat_1(X0) = X1 ),
% 2.79/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_399,plain,
% 2.79/1.00      ( k1_relat_1(X0) = X1
% 2.79/1.00      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6,plain,
% 2.79/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_398,plain,
% 2.79/1.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.79/1.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1871,plain,
% 2.79/1.00      ( k1_relat_1(X0) = X1
% 2.79/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_399,c_398]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2530,plain,
% 2.79/1.00      ( k1_relat_1(sK3(X0,X1)) = X2
% 2.79/1.00      | r2_hidden(sK0(sK3(X0,X1),X2),X0) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(sK3(X0,X1),X2),X2) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_9,c_1871]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2624,plain,
% 2.79/1.00      ( X0 = X1
% 2.79/1.00      | r2_hidden(sK0(sK3(X1,X2),X0),X1) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(sK3(X1,X2),X0),X0) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_2530,c_9]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4245,plain,
% 2.79/1.00      ( sK5 = X0
% 2.79/1.00      | r2_hidden(sK0(sK3(sK5,X1),X0),X0) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_1151,c_2624]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4432,plain,
% 2.79/1.00      ( sK5 = X0
% 2.79/1.00      | r2_hidden(sK0(sK4(sK5),X0),X0) = iProver_top
% 2.79/1.00      | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_4245,c_1151]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_0,plain,
% 2.79/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3,plain,
% 2.79/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_401,plain,
% 2.79/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1361,plain,
% 2.79/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_0,c_401]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4925,plain,
% 2.79/1.00      ( sK5 = k1_xboole_0
% 2.79/1.00      | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_4432,c_1361]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_16,negated_conjecture,
% 2.79/1.00      ( k1_xboole_0 != sK5 ),
% 2.79/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2,plain,
% 2.79/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.79/1.00      | k1_xboole_0 = X1
% 2.79/1.00      | k1_xboole_0 = X0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_56,plain,
% 2.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.79/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1,plain,
% 2.79/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_57,plain,
% 2.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_158,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_530,plain,
% 2.79/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_158]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_531,plain,
% 2.79/1.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_530]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5476,plain,
% 2.79/1.00      ( r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_4925,c_16,c_56,c_57,c_531]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_8,plain,
% 2.79/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1,X2),X0) = X2 ),
% 2.79/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_396,plain,
% 2.79/1.00      ( k1_funct_1(sK3(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5485,plain,
% 2.79/1.00      ( k1_funct_1(sK3(sK5,X0),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_5476,c_396]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5504,plain,
% 2.79/1.00      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_5485,c_1151]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5611,plain,
% 2.79/1.00      ( X0 = X1 ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_5504,c_5504]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6045,plain,
% 2.79/1.00      ( k1_xboole_0 != X0 ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_5611,c_16]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6056,plain,
% 2.79/1.00      ( $false ),
% 2.79/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6045,c_5611]) ).
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  ------                               Statistics
% 2.79/1.00  
% 2.79/1.00  ------ General
% 2.79/1.00  
% 2.79/1.00  abstr_ref_over_cycles:                  0
% 2.79/1.00  abstr_ref_under_cycles:                 0
% 2.79/1.00  gc_basic_clause_elim:                   0
% 2.79/1.00  forced_gc_time:                         0
% 2.79/1.00  parsing_time:                           0.01
% 2.79/1.00  unif_index_cands_time:                  0.
% 2.79/1.00  unif_index_add_time:                    0.
% 2.79/1.00  orderings_time:                         0.
% 2.79/1.00  out_proof_time:                         0.006
% 2.79/1.00  total_time:                             0.239
% 2.79/1.00  num_of_symbols:                         45
% 2.79/1.00  num_of_terms:                           7795
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing
% 2.79/1.00  
% 2.79/1.00  num_of_splits:                          0
% 2.79/1.00  num_of_split_atoms:                     0
% 2.79/1.00  num_of_reused_defs:                     0
% 2.79/1.00  num_eq_ax_congr_red:                    20
% 2.79/1.00  num_of_sem_filtered_clauses:            1
% 2.79/1.00  num_of_subtypes:                        0
% 2.79/1.00  monotx_restored_types:                  0
% 2.79/1.00  sat_num_of_epr_types:                   0
% 2.79/1.00  sat_num_of_non_cyclic_types:            0
% 2.79/1.00  sat_guarded_non_collapsed_types:        0
% 2.79/1.00  num_pure_diseq_elim:                    0
% 2.79/1.00  simp_replaced_by:                       0
% 2.79/1.00  res_preprocessed:                       73
% 2.79/1.00  prep_upred:                             0
% 2.79/1.00  prep_unflattend:                        0
% 2.79/1.00  smt_new_axioms:                         0
% 2.79/1.00  pred_elim_cands:                        3
% 2.79/1.00  pred_elim:                              0
% 2.79/1.00  pred_elim_cl:                           0
% 2.79/1.00  pred_elim_cycles:                       1
% 2.79/1.00  merged_defs:                            0
% 2.79/1.00  merged_defs_ncl:                        0
% 2.79/1.00  bin_hyper_res:                          0
% 2.79/1.00  prep_cycles:                            3
% 2.79/1.00  pred_elim_time:                         0.
% 2.79/1.00  splitting_time:                         0.
% 2.79/1.00  sem_filter_time:                        0.
% 2.79/1.00  monotx_time:                            0.
% 2.79/1.00  subtype_inf_time:                       0.
% 2.79/1.00  
% 2.79/1.00  ------ Problem properties
% 2.79/1.00  
% 2.79/1.00  clauses:                                18
% 2.79/1.00  conjectures:                            2
% 2.79/1.00  epr:                                    1
% 2.79/1.00  horn:                                   16
% 2.79/1.00  ground:                                 1
% 2.79/1.00  unary:                                  10
% 2.79/1.00  binary:                                 4
% 2.79/1.00  lits:                                   34
% 2.79/1.00  lits_eq:                                15
% 2.79/1.00  fd_pure:                                0
% 2.79/1.00  fd_pseudo:                              0
% 2.79/1.00  fd_cond:                                1
% 2.79/1.00  fd_pseudo_cond:                         3
% 2.79/1.00  ac_symbols:                             0
% 2.79/1.00  
% 2.79/1.00  ------ Propositional Solver
% 2.79/1.00  
% 2.79/1.00  prop_solver_calls:                      24
% 2.79/1.00  prop_fast_solver_calls:                 489
% 2.79/1.00  smt_solver_calls:                       0
% 2.79/1.00  smt_fast_solver_calls:                  0
% 2.79/1.00  prop_num_of_clauses:                    2259
% 2.79/1.00  prop_preprocess_simplified:             5001
% 2.79/1.00  prop_fo_subsumed:                       25
% 2.79/1.00  prop_solver_time:                       0.
% 2.79/1.00  smt_solver_time:                        0.
% 2.79/1.00  smt_fast_solver_time:                   0.
% 2.79/1.00  prop_fast_solver_time:                  0.
% 2.79/1.00  prop_unsat_core_time:                   0.
% 2.79/1.00  
% 2.79/1.00  ------ QBF
% 2.79/1.00  
% 2.79/1.00  qbf_q_res:                              0
% 2.79/1.00  qbf_num_tautologies:                    0
% 2.79/1.00  qbf_prep_cycles:                        0
% 2.79/1.00  
% 2.79/1.00  ------ BMC1
% 2.79/1.00  
% 2.79/1.00  bmc1_current_bound:                     -1
% 2.79/1.00  bmc1_last_solved_bound:                 -1
% 2.79/1.00  bmc1_unsat_core_size:                   -1
% 2.79/1.00  bmc1_unsat_core_parents_size:           -1
% 2.79/1.00  bmc1_merge_next_fun:                    0
% 2.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation
% 2.79/1.00  
% 2.79/1.00  inst_num_of_clauses:                    586
% 2.79/1.00  inst_num_in_passive:                    205
% 2.79/1.00  inst_num_in_active:                     279
% 2.79/1.00  inst_num_in_unprocessed:                102
% 2.79/1.00  inst_num_of_loops:                      320
% 2.79/1.00  inst_num_of_learning_restarts:          0
% 2.79/1.00  inst_num_moves_active_passive:          38
% 2.79/1.00  inst_lit_activity:                      0
% 2.79/1.00  inst_lit_activity_moves:                0
% 2.79/1.00  inst_num_tautologies:                   0
% 2.79/1.00  inst_num_prop_implied:                  0
% 2.79/1.00  inst_num_existing_simplified:           0
% 2.79/1.00  inst_num_eq_res_simplified:             0
% 2.79/1.00  inst_num_child_elim:                    0
% 2.79/1.00  inst_num_of_dismatching_blockings:      206
% 2.79/1.00  inst_num_of_non_proper_insts:           596
% 2.79/1.00  inst_num_of_duplicates:                 0
% 2.79/1.00  inst_inst_num_from_inst_to_res:         0
% 2.79/1.00  inst_dismatching_checking_time:         0.
% 2.79/1.00  
% 2.79/1.00  ------ Resolution
% 2.79/1.00  
% 2.79/1.00  res_num_of_clauses:                     0
% 2.79/1.00  res_num_in_passive:                     0
% 2.79/1.00  res_num_in_active:                      0
% 2.79/1.00  res_num_of_loops:                       76
% 2.79/1.00  res_forward_subset_subsumed:            25
% 2.79/1.00  res_backward_subset_subsumed:           0
% 2.79/1.00  res_forward_subsumed:                   0
% 2.79/1.00  res_backward_subsumed:                  0
% 2.79/1.00  res_forward_subsumption_resolution:     0
% 2.79/1.00  res_backward_subsumption_resolution:    0
% 2.79/1.00  res_clause_to_clause_subsumption:       792
% 2.79/1.00  res_orphan_elimination:                 0
% 2.79/1.00  res_tautology_del:                      17
% 2.79/1.00  res_num_eq_res_simplified:              0
% 2.79/1.00  res_num_sel_changes:                    0
% 2.79/1.00  res_moves_from_active_to_pass:          0
% 2.79/1.00  
% 2.79/1.00  ------ Superposition
% 2.79/1.00  
% 2.79/1.00  sup_time_total:                         0.
% 2.79/1.00  sup_time_generating:                    0.
% 2.79/1.00  sup_time_sim_full:                      0.
% 2.79/1.00  sup_time_sim_immed:                     0.
% 2.79/1.00  
% 2.79/1.00  sup_num_of_clauses:                     183
% 2.79/1.00  sup_num_in_active:                      9
% 2.79/1.00  sup_num_in_passive:                     174
% 2.79/1.00  sup_num_of_loops:                       63
% 2.79/1.00  sup_fw_superposition:                   126
% 2.79/1.00  sup_bw_superposition:                   257
% 2.79/1.00  sup_immediate_simplified:               112
% 2.79/1.00  sup_given_eliminated:                   2
% 2.79/1.00  comparisons_done:                       0
% 2.79/1.00  comparisons_avoided:                    3
% 2.79/1.00  
% 2.79/1.00  ------ Simplifications
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  sim_fw_subset_subsumed:                 25
% 2.79/1.00  sim_bw_subset_subsumed:                 57
% 2.79/1.00  sim_fw_subsumed:                        67
% 2.79/1.00  sim_bw_subsumed:                        7
% 2.79/1.00  sim_fw_subsumption_res:                 32
% 2.79/1.00  sim_bw_subsumption_res:                 0
% 2.79/1.00  sim_tautology_del:                      13
% 2.79/1.00  sim_eq_tautology_del:                   27
% 2.79/1.00  sim_eq_res_simp:                        0
% 2.79/1.00  sim_fw_demodulated:                     11
% 2.79/1.00  sim_bw_demodulated:                     70
% 2.79/1.00  sim_light_normalised:                   21
% 2.79/1.00  sim_joinable_taut:                      0
% 2.79/1.00  sim_joinable_simp:                      0
% 2.79/1.00  sim_ac_normalised:                      0
% 2.79/1.00  sim_smt_subsumption:                    0
% 2.79/1.00  
%------------------------------------------------------------------------------
