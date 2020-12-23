%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:20 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 229 expanded)
%              Number of clauses        :   51 (  85 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  298 ( 934 expanded)
%              Number of equality atoms :  157 ( 421 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK5(X0)) = X0
      & v1_funct_1(sK5(X0))
      & v1_relat_1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f36])).

fof(f61,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK6(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK6(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f38])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f40,plain,
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
   => ( k1_xboole_0 != sK7
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK7
              | k1_relat_1(X1) != sK7
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_xboole_0 != sK7
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK7
            | k1_relat_1(X1) != sK7
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f40])).

fof(f67,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK7
      | k1_relat_1(X1) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0] :
      ( k1_funct_1(sK6(X0),X2) = np__1
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21059,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21054,plain,
    ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22370,plain,
    ( k1_funct_1(sK5(X0),sK0(X0)) = k1_xboole_0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21059,c_21054])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21057,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21056,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21058,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_22378,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21056,c_21058])).

cnf(c_22850,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22378,c_21058])).

cnf(c_23012,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21057,c_22850])).

cnf(c_23035,plain,
    ( k1_funct_1(sK5(X0),sK0(X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_22370,c_23012])).

cnf(c_21,plain,
    ( k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,plain,
    ( k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK7
    | k1_relat_1(X1) != sK7 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21049,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK7
    | k1_relat_1(X1) != sK7
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21224,plain,
    ( sK5(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_21049])).

cnf(c_19,plain,
    ( v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_41,plain,
    ( v1_relat_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_44,plain,
    ( v1_funct_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21320,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK5(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21224,c_41,c_44])).

cnf(c_21321,plain,
    ( sK5(X0) = X1
    | k1_relat_1(X1) != sK7
    | sK7 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21320])).

cnf(c_21566,plain,
    ( sK6(X0) = sK5(X1)
    | sK7 != X0
    | sK7 != X1
    | v1_funct_1(sK6(X0)) != iProver_top
    | v1_relat_1(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_21321])).

cnf(c_23,plain,
    ( v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,plain,
    ( v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21592,plain,
    ( ~ v1_funct_1(sK6(X0))
    | ~ v1_relat_1(sK6(X0))
    | sK6(X0) = sK5(X1)
    | sK7 != X0
    | sK7 != X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21566])).

cnf(c_21790,plain,
    ( sK6(X0) = sK5(X1)
    | sK7 != X0
    | sK7 != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21566,c_23,c_22,c_21592])).

cnf(c_21795,plain,
    ( sK5(X0) = sK6(sK7)
    | sK7 != X0 ),
    inference(equality_resolution,[status(thm)],[c_21790])).

cnf(c_21927,plain,
    ( sK6(sK7) = sK5(sK7) ),
    inference(equality_resolution,[status(thm)],[c_21795])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK6(X1),X0) = np__1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21052,plain,
    ( k1_funct_1(sK6(X0),X1) = np__1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22230,plain,
    ( k1_funct_1(sK6(X0),sK0(X0)) = np__1
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21059,c_21052])).

cnf(c_23036,plain,
    ( k1_funct_1(sK6(X0),sK0(X0)) = np__1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_22230,c_23012])).

cnf(c_23249,plain,
    ( k1_funct_1(sK5(sK7),sK0(sK7)) = np__1
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21927,c_23036])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_215,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_232,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_216,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1994,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1995,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_23310,plain,
    ( k1_funct_1(sK5(sK7),sK0(sK7)) = np__1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23249,c_25,c_232,c_1995])).

cnf(c_23313,plain,
    ( sK7 = k1_xboole_0
    | np__1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23035,c_23310])).

cnf(c_217,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2066,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(np__1)
    | np__1 != X0 ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_2068,plain,
    ( v1_xboole_0(np__1)
    | ~ v1_xboole_0(k1_xboole_0)
    | np__1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23313,c_2068,c_1995,c_232,c_2,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.78/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.49  
% 7.78/1.49  ------  iProver source info
% 7.78/1.49  
% 7.78/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.49  git: non_committed_changes: false
% 7.78/1.49  git: last_make_outside_of_git: false
% 7.78/1.49  
% 7.78/1.49  ------ 
% 7.78/1.49  ------ Parsing...
% 7.78/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  ------ Proving...
% 7.78/1.49  ------ Problem Properties 
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  clauses                                 27
% 7.78/1.49  conjectures                             2
% 7.78/1.49  EPR                                     5
% 7.78/1.49  Horn                                    23
% 7.78/1.49  unary                                   11
% 7.78/1.49  binary                                  5
% 7.78/1.49  lits                                    68
% 7.78/1.49  lits eq                                 22
% 7.78/1.49  fd_pure                                 0
% 7.78/1.49  fd_pseudo                               0
% 7.78/1.49  fd_cond                                 2
% 7.78/1.49  fd_pseudo_cond                          6
% 7.78/1.49  AC symbols                              0
% 7.78/1.49  
% 7.78/1.49  ------ Input Options Time Limit: Unbounded
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing...
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.78/1.49  Current options:
% 7.78/1.49  ------ 
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS status Theorem for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  fof(f1,axiom,(
% 7.78/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f23,plain,(
% 7.78/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.78/1.49    inference(nnf_transformation,[],[f1])).
% 7.78/1.49  
% 7.78/1.49  fof(f24,plain,(
% 7.78/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.78/1.49    inference(rectify,[],[f23])).
% 7.78/1.49  
% 7.78/1.49  fof(f25,plain,(
% 7.78/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f26,plain,(
% 7.78/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.78/1.49  
% 7.78/1.49  fof(f43,plain,(
% 7.78/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f26])).
% 7.78/1.49  
% 7.78/1.49  fof(f8,axiom,(
% 7.78/1.49    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f19,plain,(
% 7.78/1.49    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.49    inference(ennf_transformation,[],[f8])).
% 7.78/1.49  
% 7.78/1.49  fof(f36,plain,(
% 7.78/1.49    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f37,plain,(
% 7.78/1.49    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f36])).
% 7.78/1.49  
% 7.78/1.49  fof(f61,plain,(
% 7.78/1.49    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f37])).
% 7.78/1.49  
% 7.78/1.49  fof(f2,axiom,(
% 7.78/1.49    v1_xboole_0(k1_xboole_0)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f44,plain,(
% 7.78/1.49    v1_xboole_0(k1_xboole_0)),
% 7.78/1.49    inference(cnf_transformation,[],[f2])).
% 7.78/1.49  
% 7.78/1.49  fof(f3,axiom,(
% 7.78/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f13,plain,(
% 7.78/1.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.78/1.49    inference(ennf_transformation,[],[f3])).
% 7.78/1.49  
% 7.78/1.49  fof(f27,plain,(
% 7.78/1.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.78/1.49    inference(nnf_transformation,[],[f13])).
% 7.78/1.49  
% 7.78/1.49  fof(f28,plain,(
% 7.78/1.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f29,plain,(
% 7.78/1.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.78/1.49  
% 7.78/1.49  fof(f45,plain,(
% 7.78/1.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f29])).
% 7.78/1.49  
% 7.78/1.49  fof(f42,plain,(
% 7.78/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f26])).
% 7.78/1.49  
% 7.78/1.49  fof(f9,axiom,(
% 7.78/1.49    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f20,plain,(
% 7.78/1.49    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.49    inference(ennf_transformation,[],[f9])).
% 7.78/1.49  
% 7.78/1.49  fof(f38,plain,(
% 7.78/1.49    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK6(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f39,plain,(
% 7.78/1.49    ! [X0] : (! [X2] : (k1_funct_1(sK6(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f38])).
% 7.78/1.49  
% 7.78/1.49  fof(f64,plain,(
% 7.78/1.49    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 7.78/1.49    inference(cnf_transformation,[],[f39])).
% 7.78/1.49  
% 7.78/1.49  fof(f60,plain,(
% 7.78/1.49    ( ! [X0] : (k1_relat_1(sK5(X0)) = X0) )),
% 7.78/1.49    inference(cnf_transformation,[],[f37])).
% 7.78/1.49  
% 7.78/1.49  fof(f11,conjecture,(
% 7.78/1.49    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f12,negated_conjecture,(
% 7.78/1.49    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.78/1.49    inference(negated_conjecture,[],[f11])).
% 7.78/1.49  
% 7.78/1.49  fof(f21,plain,(
% 7.78/1.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 7.78/1.49    inference(ennf_transformation,[],[f12])).
% 7.78/1.49  
% 7.78/1.49  fof(f22,plain,(
% 7.78/1.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.78/1.49    inference(flattening,[],[f21])).
% 7.78/1.49  
% 7.78/1.49  fof(f40,plain,(
% 7.78/1.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK7 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f41,plain,(
% 7.78/1.50    k1_xboole_0 != sK7 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.78/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f40])).
% 7.78/1.50  
% 7.78/1.50  fof(f67,plain,(
% 7.78/1.50    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK7 | k1_relat_1(X1) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f41])).
% 7.78/1.50  
% 7.78/1.50  fof(f58,plain,(
% 7.78/1.50    ( ! [X0] : (v1_relat_1(sK5(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f37])).
% 7.78/1.50  
% 7.78/1.50  fof(f59,plain,(
% 7.78/1.50    ( ! [X0] : (v1_funct_1(sK5(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f37])).
% 7.78/1.50  
% 7.78/1.50  fof(f62,plain,(
% 7.78/1.50    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f39])).
% 7.78/1.50  
% 7.78/1.50  fof(f63,plain,(
% 7.78/1.50    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f39])).
% 7.78/1.50  
% 7.78/1.50  fof(f65,plain,(
% 7.78/1.50    ( ! [X2,X0] : (k1_funct_1(sK6(X0),X2) = np__1 | ~r2_hidden(X2,X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f39])).
% 7.78/1.50  
% 7.78/1.50  fof(f68,plain,(
% 7.78/1.50    k1_xboole_0 != sK7),
% 7.78/1.50    inference(cnf_transformation,[],[f41])).
% 7.78/1.50  
% 7.78/1.50  fof(f10,axiom,(
% 7.78/1.50    ~v1_xboole_0(np__1)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f66,plain,(
% 7.78/1.50    ~v1_xboole_0(np__1)),
% 7.78/1.50    inference(cnf_transformation,[],[f10])).
% 7.78/1.50  
% 7.78/1.50  cnf(c_0,plain,
% 7.78/1.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21059,plain,
% 7.78/1.50      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.78/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_16,plain,
% 7.78/1.50      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
% 7.78/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21054,plain,
% 7.78/1.50      ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
% 7.78/1.50      | r2_hidden(X1,X0) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_22370,plain,
% 7.78/1.50      ( k1_funct_1(sK5(X0),sK0(X0)) = k1_xboole_0
% 7.78/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21059,c_21054]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_2,plain,
% 7.78/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21057,plain,
% 7.78/1.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_4,plain,
% 7.78/1.50      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 7.78/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21056,plain,
% 7.78/1.50      ( X0 = X1
% 7.78/1.50      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 7.78/1.50      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1,plain,
% 7.78/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21058,plain,
% 7.78/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.78/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_22378,plain,
% 7.78/1.50      ( X0 = X1
% 7.78/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 7.78/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21056,c_21058]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_22850,plain,
% 7.78/1.50      ( X0 = X1
% 7.78/1.50      | v1_xboole_0(X1) != iProver_top
% 7.78/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_22378,c_21058]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23012,plain,
% 7.78/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21057,c_22850]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23035,plain,
% 7.78/1.50      ( k1_funct_1(sK5(X0),sK0(X0)) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_22370,c_23012]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21,plain,
% 7.78/1.50      ( k1_relat_1(sK6(X0)) = X0 ),
% 7.78/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_17,plain,
% 7.78/1.50      ( k1_relat_1(sK5(X0)) = X0 ),
% 7.78/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_26,negated_conjecture,
% 7.78/1.50      ( ~ v1_funct_1(X0)
% 7.78/1.50      | ~ v1_funct_1(X1)
% 7.78/1.50      | ~ v1_relat_1(X0)
% 7.78/1.50      | ~ v1_relat_1(X1)
% 7.78/1.50      | X1 = X0
% 7.78/1.50      | k1_relat_1(X0) != sK7
% 7.78/1.50      | k1_relat_1(X1) != sK7 ),
% 7.78/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21049,plain,
% 7.78/1.50      ( X0 = X1
% 7.78/1.50      | k1_relat_1(X0) != sK7
% 7.78/1.50      | k1_relat_1(X1) != sK7
% 7.78/1.50      | v1_funct_1(X1) != iProver_top
% 7.78/1.50      | v1_funct_1(X0) != iProver_top
% 7.78/1.50      | v1_relat_1(X1) != iProver_top
% 7.78/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21224,plain,
% 7.78/1.50      ( sK5(X0) = X1
% 7.78/1.50      | k1_relat_1(X1) != sK7
% 7.78/1.50      | sK7 != X0
% 7.78/1.50      | v1_funct_1(X1) != iProver_top
% 7.78/1.50      | v1_funct_1(sK5(X0)) != iProver_top
% 7.78/1.50      | v1_relat_1(X1) != iProver_top
% 7.78/1.50      | v1_relat_1(sK5(X0)) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_17,c_21049]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_19,plain,
% 7.78/1.50      ( v1_relat_1(sK5(X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_41,plain,
% 7.78/1.50      ( v1_relat_1(sK5(X0)) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_18,plain,
% 7.78/1.50      ( v1_funct_1(sK5(X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_44,plain,
% 7.78/1.50      ( v1_funct_1(sK5(X0)) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21320,plain,
% 7.78/1.50      ( v1_relat_1(X1) != iProver_top
% 7.78/1.50      | sK5(X0) = X1
% 7.78/1.50      | k1_relat_1(X1) != sK7
% 7.78/1.50      | sK7 != X0
% 7.78/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.50      inference(global_propositional_subsumption,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_21224,c_41,c_44]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21321,plain,
% 7.78/1.50      ( sK5(X0) = X1
% 7.78/1.50      | k1_relat_1(X1) != sK7
% 7.78/1.50      | sK7 != X0
% 7.78/1.50      | v1_funct_1(X1) != iProver_top
% 7.78/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.50      inference(renaming,[status(thm)],[c_21320]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21566,plain,
% 7.78/1.50      ( sK6(X0) = sK5(X1)
% 7.78/1.50      | sK7 != X0
% 7.78/1.50      | sK7 != X1
% 7.78/1.50      | v1_funct_1(sK6(X0)) != iProver_top
% 7.78/1.50      | v1_relat_1(sK6(X0)) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21,c_21321]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23,plain,
% 7.78/1.50      ( v1_relat_1(sK6(X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_22,plain,
% 7.78/1.50      ( v1_funct_1(sK6(X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21592,plain,
% 7.78/1.50      ( ~ v1_funct_1(sK6(X0))
% 7.78/1.50      | ~ v1_relat_1(sK6(X0))
% 7.78/1.50      | sK6(X0) = sK5(X1)
% 7.78/1.50      | sK7 != X0
% 7.78/1.50      | sK7 != X1 ),
% 7.78/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_21566]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21790,plain,
% 7.78/1.50      ( sK6(X0) = sK5(X1) | sK7 != X0 | sK7 != X1 ),
% 7.78/1.50      inference(global_propositional_subsumption,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_21566,c_23,c_22,c_21592]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21795,plain,
% 7.78/1.50      ( sK5(X0) = sK6(sK7) | sK7 != X0 ),
% 7.78/1.50      inference(equality_resolution,[status(thm)],[c_21790]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21927,plain,
% 7.78/1.50      ( sK6(sK7) = sK5(sK7) ),
% 7.78/1.50      inference(equality_resolution,[status(thm)],[c_21795]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_20,plain,
% 7.78/1.50      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK6(X1),X0) = np__1 ),
% 7.78/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_21052,plain,
% 7.78/1.50      ( k1_funct_1(sK6(X0),X1) = np__1
% 7.78/1.50      | r2_hidden(X1,X0) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_22230,plain,
% 7.78/1.50      ( k1_funct_1(sK6(X0),sK0(X0)) = np__1
% 7.78/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21059,c_21052]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23036,plain,
% 7.78/1.50      ( k1_funct_1(sK6(X0),sK0(X0)) = np__1 | k1_xboole_0 = X0 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_22230,c_23012]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23249,plain,
% 7.78/1.50      ( k1_funct_1(sK5(sK7),sK0(sK7)) = np__1 | sK7 = k1_xboole_0 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_21927,c_23036]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_25,negated_conjecture,
% 7.78/1.50      ( k1_xboole_0 != sK7 ),
% 7.78/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_215,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_232,plain,
% 7.78/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_215]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_216,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1994,plain,
% 7.78/1.50      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_216]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1995,plain,
% 7.78/1.50      ( sK7 != k1_xboole_0
% 7.78/1.50      | k1_xboole_0 = sK7
% 7.78/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_1994]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23310,plain,
% 7.78/1.50      ( k1_funct_1(sK5(sK7),sK0(sK7)) = np__1 ),
% 7.78/1.50      inference(global_propositional_subsumption,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_23249,c_25,c_232,c_1995]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_23313,plain,
% 7.78/1.50      ( sK7 = k1_xboole_0 | np__1 = k1_xboole_0 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_23035,c_23310]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_217,plain,
% 7.78/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.78/1.50      theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_2066,plain,
% 7.78/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(np__1) | np__1 != X0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_217]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_2068,plain,
% 7.78/1.50      ( v1_xboole_0(np__1)
% 7.78/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.78/1.50      | np__1 != k1_xboole_0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_2066]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_24,plain,
% 7.78/1.50      ( ~ v1_xboole_0(np__1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(contradiction,plain,
% 7.78/1.50      ( $false ),
% 7.78/1.50      inference(minisat,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_23313,c_2068,c_1995,c_232,c_2,c_24,c_25]) ).
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  ------                               Statistics
% 7.78/1.50  
% 7.78/1.50  ------ Selected
% 7.78/1.50  
% 7.78/1.50  total_time:                             0.61
% 7.78/1.50  
%------------------------------------------------------------------------------
