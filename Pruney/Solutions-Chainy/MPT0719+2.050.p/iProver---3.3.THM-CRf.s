%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:09 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   93 (2575 expanded)
%              Number of clauses        :   57 (1079 expanded)
%              Number of leaves         :   13 ( 591 expanded)
%              Depth                    :   18
%              Number of atoms          :  270 (8326 expanded)
%              Number of equality atoms :  129 (3063 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1)))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1)))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK1(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f40,plain,(
    ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | ~ r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X1))
    | v5_funct_1(X1,X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_528,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X1)) = iProver_top
    | v5_funct_1(X1,X0) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK1(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_524,plain,
    ( k1_funct_1(sK1(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1440,plain,
    ( k1_funct_1(sK1(k1_relat_1(X0),X1),sK0(X2,X0)) = X1
    | v5_funct_1(X0,X2) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_524])).

cnf(c_14,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_521,plain,
    ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1561,plain,
    ( k1_funct_1(sK1(k1_relat_1(k1_xboole_0),X0),sK0(sK2,k1_xboole_0)) = X0
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_521])).

cnf(c_1,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,plain,
    ( k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_530,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1187,plain,
    ( sK1(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_530])).

cnf(c_13,plain,
    ( v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,plain,
    ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1285,plain,
    ( k1_xboole_0 != X0
    | sK1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_20])).

cnf(c_1286,plain,
    ( sK1(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_1285])).

cnf(c_1290,plain,
    ( sK1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1286])).

cnf(c_1562,plain,
    ( k1_funct_1(k1_xboole_0,sK0(sK2,k1_xboole_0)) = X0
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1561,c_1,c_1290])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_33,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_35,plain,
    ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_263,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_282,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_272,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_657,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_658,plain,
    ( X0 != k6_relat_1(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_660,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_525,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_825,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_525])).

cnf(c_264,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_905,plain,
    ( X0 != X1
    | X0 = k6_relat_1(X2)
    | k6_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_906,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1567,plain,
    ( k1_funct_1(k1_xboole_0,sK0(sK2,k1_xboole_0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1562,c_17,c_18,c_35,c_4,c_282,c_660,c_825,c_906])).

cnf(c_1578,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_1567,c_1567])).

cnf(c_5,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(X1,X0)),k1_funct_1(X1,sK0(X1,X0)))
    | v5_funct_1(X0,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_529,plain,
    ( r2_hidden(k1_funct_1(X0,sK0(X1,X0)),k1_funct_1(X1,sK0(X1,X0))) != iProver_top
    | v5_funct_1(X0,X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1575,plain,
    ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top
    | v5_funct_1(k1_xboole_0,sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_529])).

cnf(c_1933,plain,
    ( v1_relat_1(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1578,c_525])).

cnf(c_526,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1932,plain,
    ( v1_funct_1(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1578,c_526])).

cnf(c_2121,plain,
    ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top
    | v5_funct_1(k1_xboole_0,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1575,c_1933,c_1933,c_1932,c_1932])).

cnf(c_19,plain,
    ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2510,plain,
    ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_19])).

cnf(c_2517,plain,
    ( r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_2510])).

cnf(c_1922,plain,
    ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top
    | v5_funct_1(X0,X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1578,c_528])).

cnf(c_1995,plain,
    ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top
    | v5_funct_1(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1922,c_1933,c_1933,c_1932,c_1932])).

cnf(c_2195,plain,
    ( v5_funct_1(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_521])).

cnf(c_2218,plain,
    ( v5_funct_1(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_2195])).

cnf(c_2714,plain,
    ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1995,c_2218])).

cnf(c_2732,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2517,c_2714])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.21/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.00  
% 2.21/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.00  
% 2.21/1.00  ------  iProver source info
% 2.21/1.00  
% 2.21/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.00  git: non_committed_changes: false
% 2.21/1.00  git: last_make_outside_of_git: false
% 2.21/1.00  
% 2.21/1.00  ------ 
% 2.21/1.00  
% 2.21/1.00  ------ Input Options
% 2.21/1.00  
% 2.21/1.00  --out_options                           all
% 2.21/1.00  --tptp_safe_out                         true
% 2.21/1.00  --problem_path                          ""
% 2.21/1.00  --include_path                          ""
% 2.21/1.00  --clausifier                            res/vclausify_rel
% 2.21/1.00  --clausifier_options                    --mode clausify
% 2.21/1.00  --stdin                                 false
% 2.21/1.00  --stats_out                             all
% 2.21/1.00  
% 2.21/1.00  ------ General Options
% 2.21/1.00  
% 2.21/1.00  --fof                                   false
% 2.21/1.00  --time_out_real                         305.
% 2.21/1.00  --time_out_virtual                      -1.
% 2.21/1.00  --symbol_type_check                     false
% 2.21/1.00  --clausify_out                          false
% 2.21/1.00  --sig_cnt_out                           false
% 2.21/1.00  --trig_cnt_out                          false
% 2.21/1.00  --trig_cnt_out_tolerance                1.
% 2.21/1.00  --trig_cnt_out_sk_spl                   false
% 2.21/1.00  --abstr_cl_out                          false
% 2.21/1.00  
% 2.21/1.00  ------ Global Options
% 2.21/1.00  
% 2.21/1.00  --schedule                              default
% 2.21/1.00  --add_important_lit                     false
% 2.21/1.00  --prop_solver_per_cl                    1000
% 2.21/1.00  --min_unsat_core                        false
% 2.21/1.00  --soft_assumptions                      false
% 2.21/1.00  --soft_lemma_size                       3
% 2.21/1.00  --prop_impl_unit_size                   0
% 2.21/1.00  --prop_impl_unit                        []
% 2.21/1.00  --share_sel_clauses                     true
% 2.21/1.00  --reset_solvers                         false
% 2.21/1.00  --bc_imp_inh                            [conj_cone]
% 2.21/1.00  --conj_cone_tolerance                   3.
% 2.21/1.00  --extra_neg_conj                        none
% 2.21/1.00  --large_theory_mode                     true
% 2.21/1.00  --prolific_symb_bound                   200
% 2.21/1.00  --lt_threshold                          2000
% 2.21/1.00  --clause_weak_htbl                      true
% 2.21/1.00  --gc_record_bc_elim                     false
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing Options
% 2.21/1.00  
% 2.21/1.00  --preprocessing_flag                    true
% 2.21/1.00  --time_out_prep_mult                    0.1
% 2.21/1.00  --splitting_mode                        input
% 2.21/1.00  --splitting_grd                         true
% 2.21/1.00  --splitting_cvd                         false
% 2.21/1.00  --splitting_cvd_svl                     false
% 2.21/1.00  --splitting_nvd                         32
% 2.21/1.00  --sub_typing                            true
% 2.21/1.00  --prep_gs_sim                           true
% 2.21/1.00  --prep_unflatten                        true
% 2.21/1.00  --prep_res_sim                          true
% 2.21/1.00  --prep_upred                            true
% 2.21/1.00  --prep_sem_filter                       exhaustive
% 2.21/1.00  --prep_sem_filter_out                   false
% 2.21/1.00  --pred_elim                             true
% 2.21/1.00  --res_sim_input                         true
% 2.21/1.00  --eq_ax_congr_red                       true
% 2.21/1.00  --pure_diseq_elim                       true
% 2.21/1.00  --brand_transform                       false
% 2.21/1.00  --non_eq_to_eq                          false
% 2.21/1.00  --prep_def_merge                        true
% 2.21/1.00  --prep_def_merge_prop_impl              false
% 2.21/1.00  --prep_def_merge_mbd                    true
% 2.21/1.00  --prep_def_merge_tr_red                 false
% 2.21/1.00  --prep_def_merge_tr_cl                  false
% 2.21/1.00  --smt_preprocessing                     true
% 2.21/1.00  --smt_ac_axioms                         fast
% 2.21/1.00  --preprocessed_out                      false
% 2.21/1.00  --preprocessed_stats                    false
% 2.21/1.00  
% 2.21/1.00  ------ Abstraction refinement Options
% 2.21/1.00  
% 2.21/1.00  --abstr_ref                             []
% 2.21/1.00  --abstr_ref_prep                        false
% 2.21/1.00  --abstr_ref_until_sat                   false
% 2.21/1.00  --abstr_ref_sig_restrict                funpre
% 2.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.00  --abstr_ref_under                       []
% 2.21/1.00  
% 2.21/1.00  ------ SAT Options
% 2.21/1.00  
% 2.21/1.00  --sat_mode                              false
% 2.21/1.00  --sat_fm_restart_options                ""
% 2.21/1.00  --sat_gr_def                            false
% 2.21/1.00  --sat_epr_types                         true
% 2.21/1.00  --sat_non_cyclic_types                  false
% 2.21/1.00  --sat_finite_models                     false
% 2.21/1.00  --sat_fm_lemmas                         false
% 2.21/1.00  --sat_fm_prep                           false
% 2.21/1.00  --sat_fm_uc_incr                        true
% 2.21/1.00  --sat_out_model                         small
% 2.21/1.00  --sat_out_clauses                       false
% 2.21/1.00  
% 2.21/1.00  ------ QBF Options
% 2.21/1.00  
% 2.21/1.00  --qbf_mode                              false
% 2.21/1.00  --qbf_elim_univ                         false
% 2.21/1.00  --qbf_dom_inst                          none
% 2.21/1.00  --qbf_dom_pre_inst                      false
% 2.21/1.00  --qbf_sk_in                             false
% 2.21/1.00  --qbf_pred_elim                         true
% 2.21/1.00  --qbf_split                             512
% 2.21/1.00  
% 2.21/1.00  ------ BMC1 Options
% 2.21/1.00  
% 2.21/1.00  --bmc1_incremental                      false
% 2.21/1.00  --bmc1_axioms                           reachable_all
% 2.21/1.00  --bmc1_min_bound                        0
% 2.21/1.00  --bmc1_max_bound                        -1
% 2.21/1.00  --bmc1_max_bound_default                -1
% 2.21/1.00  --bmc1_symbol_reachability              true
% 2.21/1.00  --bmc1_property_lemmas                  false
% 2.21/1.00  --bmc1_k_induction                      false
% 2.21/1.00  --bmc1_non_equiv_states                 false
% 2.21/1.00  --bmc1_deadlock                         false
% 2.21/1.00  --bmc1_ucm                              false
% 2.21/1.00  --bmc1_add_unsat_core                   none
% 2.21/1.00  --bmc1_unsat_core_children              false
% 2.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.00  --bmc1_out_stat                         full
% 2.21/1.00  --bmc1_ground_init                      false
% 2.21/1.00  --bmc1_pre_inst_next_state              false
% 2.21/1.00  --bmc1_pre_inst_state                   false
% 2.21/1.00  --bmc1_pre_inst_reach_state             false
% 2.21/1.00  --bmc1_out_unsat_core                   false
% 2.21/1.00  --bmc1_aig_witness_out                  false
% 2.21/1.00  --bmc1_verbose                          false
% 2.21/1.00  --bmc1_dump_clauses_tptp                false
% 2.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.00  --bmc1_dump_file                        -
% 2.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.00  --bmc1_ucm_extend_mode                  1
% 2.21/1.00  --bmc1_ucm_init_mode                    2
% 2.21/1.00  --bmc1_ucm_cone_mode                    none
% 2.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.00  --bmc1_ucm_relax_model                  4
% 2.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.00  --bmc1_ucm_layered_model                none
% 2.21/1.00  --bmc1_ucm_max_lemma_size               10
% 2.21/1.00  
% 2.21/1.00  ------ AIG Options
% 2.21/1.00  
% 2.21/1.00  --aig_mode                              false
% 2.21/1.00  
% 2.21/1.00  ------ Instantiation Options
% 2.21/1.00  
% 2.21/1.00  --instantiation_flag                    true
% 2.21/1.00  --inst_sos_flag                         false
% 2.21/1.00  --inst_sos_phase                        true
% 2.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.00  --inst_lit_sel_side                     num_symb
% 2.21/1.00  --inst_solver_per_active                1400
% 2.21/1.00  --inst_solver_calls_frac                1.
% 2.21/1.00  --inst_passive_queue_type               priority_queues
% 2.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.00  --inst_passive_queues_freq              [25;2]
% 2.21/1.00  --inst_dismatching                      true
% 2.21/1.00  --inst_eager_unprocessed_to_passive     true
% 2.21/1.00  --inst_prop_sim_given                   true
% 2.21/1.00  --inst_prop_sim_new                     false
% 2.21/1.00  --inst_subs_new                         false
% 2.21/1.00  --inst_eq_res_simp                      false
% 2.21/1.00  --inst_subs_given                       false
% 2.21/1.00  --inst_orphan_elimination               true
% 2.21/1.00  --inst_learning_loop_flag               true
% 2.21/1.00  --inst_learning_start                   3000
% 2.21/1.00  --inst_learning_factor                  2
% 2.21/1.00  --inst_start_prop_sim_after_learn       3
% 2.21/1.00  --inst_sel_renew                        solver
% 2.21/1.00  --inst_lit_activity_flag                true
% 2.21/1.00  --inst_restr_to_given                   false
% 2.21/1.00  --inst_activity_threshold               500
% 2.21/1.00  --inst_out_proof                        true
% 2.21/1.00  
% 2.21/1.00  ------ Resolution Options
% 2.21/1.00  
% 2.21/1.00  --resolution_flag                       true
% 2.21/1.00  --res_lit_sel                           adaptive
% 2.21/1.00  --res_lit_sel_side                      none
% 2.21/1.00  --res_ordering                          kbo
% 2.21/1.00  --res_to_prop_solver                    active
% 2.21/1.00  --res_prop_simpl_new                    false
% 2.21/1.00  --res_prop_simpl_given                  true
% 2.21/1.00  --res_passive_queue_type                priority_queues
% 2.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.00  --res_passive_queues_freq               [15;5]
% 2.21/1.00  --res_forward_subs                      full
% 2.21/1.00  --res_backward_subs                     full
% 2.21/1.00  --res_forward_subs_resolution           true
% 2.21/1.00  --res_backward_subs_resolution          true
% 2.21/1.00  --res_orphan_elimination                true
% 2.21/1.00  --res_time_limit                        2.
% 2.21/1.00  --res_out_proof                         true
% 2.21/1.00  
% 2.21/1.00  ------ Superposition Options
% 2.21/1.00  
% 2.21/1.00  --superposition_flag                    true
% 2.21/1.00  --sup_passive_queue_type                priority_queues
% 2.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.00  --demod_completeness_check              fast
% 2.21/1.00  --demod_use_ground                      true
% 2.21/1.00  --sup_to_prop_solver                    passive
% 2.21/1.00  --sup_prop_simpl_new                    true
% 2.21/1.00  --sup_prop_simpl_given                  true
% 2.21/1.00  --sup_fun_splitting                     false
% 2.21/1.00  --sup_smt_interval                      50000
% 2.21/1.00  
% 2.21/1.00  ------ Superposition Simplification Setup
% 2.21/1.00  
% 2.21/1.00  --sup_indices_passive                   []
% 2.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_full_bw                           [BwDemod]
% 2.21/1.00  --sup_immed_triv                        [TrivRules]
% 2.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_immed_bw_main                     []
% 2.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.00  
% 2.21/1.00  ------ Combination Options
% 2.21/1.00  
% 2.21/1.00  --comb_res_mult                         3
% 2.21/1.00  --comb_sup_mult                         2
% 2.21/1.00  --comb_inst_mult                        10
% 2.21/1.00  
% 2.21/1.00  ------ Debug Options
% 2.21/1.00  
% 2.21/1.00  --dbg_backtrace                         false
% 2.21/1.00  --dbg_dump_prop_clauses                 false
% 2.21/1.00  --dbg_dump_prop_clauses_file            -
% 2.21/1.00  --dbg_out_stat                          false
% 2.21/1.00  ------ Parsing...
% 2.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.00  ------ Proving...
% 2.21/1.00  ------ Problem Properties 
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  clauses                                 17
% 2.21/1.00  conjectures                             3
% 2.21/1.00  EPR                                     3
% 2.21/1.00  Horn                                    16
% 2.21/1.00  unary                                   11
% 2.21/1.00  binary                                  1
% 2.21/1.00  lits                                    38
% 2.21/1.00  lits eq                                 9
% 2.21/1.00  fd_pure                                 0
% 2.21/1.00  fd_pseudo                               0
% 2.21/1.00  fd_cond                                 2
% 2.21/1.00  fd_pseudo_cond                          0
% 2.21/1.00  AC symbols                              0
% 2.21/1.00  
% 2.21/1.00  ------ Schedule dynamic 5 is on 
% 2.21/1.00  
% 2.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  ------ 
% 2.21/1.00  Current options:
% 2.21/1.00  ------ 
% 2.21/1.00  
% 2.21/1.00  ------ Input Options
% 2.21/1.00  
% 2.21/1.00  --out_options                           all
% 2.21/1.00  --tptp_safe_out                         true
% 2.21/1.00  --problem_path                          ""
% 2.21/1.00  --include_path                          ""
% 2.21/1.00  --clausifier                            res/vclausify_rel
% 2.21/1.00  --clausifier_options                    --mode clausify
% 2.21/1.00  --stdin                                 false
% 2.21/1.00  --stats_out                             all
% 2.21/1.00  
% 2.21/1.00  ------ General Options
% 2.21/1.00  
% 2.21/1.00  --fof                                   false
% 2.21/1.00  --time_out_real                         305.
% 2.21/1.00  --time_out_virtual                      -1.
% 2.21/1.00  --symbol_type_check                     false
% 2.21/1.00  --clausify_out                          false
% 2.21/1.00  --sig_cnt_out                           false
% 2.21/1.00  --trig_cnt_out                          false
% 2.21/1.00  --trig_cnt_out_tolerance                1.
% 2.21/1.00  --trig_cnt_out_sk_spl                   false
% 2.21/1.00  --abstr_cl_out                          false
% 2.21/1.00  
% 2.21/1.00  ------ Global Options
% 2.21/1.00  
% 2.21/1.00  --schedule                              default
% 2.21/1.00  --add_important_lit                     false
% 2.21/1.00  --prop_solver_per_cl                    1000
% 2.21/1.00  --min_unsat_core                        false
% 2.21/1.00  --soft_assumptions                      false
% 2.21/1.00  --soft_lemma_size                       3
% 2.21/1.00  --prop_impl_unit_size                   0
% 2.21/1.00  --prop_impl_unit                        []
% 2.21/1.00  --share_sel_clauses                     true
% 2.21/1.00  --reset_solvers                         false
% 2.21/1.00  --bc_imp_inh                            [conj_cone]
% 2.21/1.00  --conj_cone_tolerance                   3.
% 2.21/1.00  --extra_neg_conj                        none
% 2.21/1.00  --large_theory_mode                     true
% 2.21/1.00  --prolific_symb_bound                   200
% 2.21/1.00  --lt_threshold                          2000
% 2.21/1.00  --clause_weak_htbl                      true
% 2.21/1.00  --gc_record_bc_elim                     false
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing Options
% 2.21/1.00  
% 2.21/1.00  --preprocessing_flag                    true
% 2.21/1.00  --time_out_prep_mult                    0.1
% 2.21/1.00  --splitting_mode                        input
% 2.21/1.00  --splitting_grd                         true
% 2.21/1.00  --splitting_cvd                         false
% 2.21/1.00  --splitting_cvd_svl                     false
% 2.21/1.00  --splitting_nvd                         32
% 2.21/1.00  --sub_typing                            true
% 2.21/1.00  --prep_gs_sim                           true
% 2.21/1.00  --prep_unflatten                        true
% 2.21/1.00  --prep_res_sim                          true
% 2.21/1.00  --prep_upred                            true
% 2.21/1.00  --prep_sem_filter                       exhaustive
% 2.21/1.00  --prep_sem_filter_out                   false
% 2.21/1.00  --pred_elim                             true
% 2.21/1.00  --res_sim_input                         true
% 2.21/1.00  --eq_ax_congr_red                       true
% 2.21/1.00  --pure_diseq_elim                       true
% 2.21/1.00  --brand_transform                       false
% 2.21/1.00  --non_eq_to_eq                          false
% 2.21/1.00  --prep_def_merge                        true
% 2.21/1.00  --prep_def_merge_prop_impl              false
% 2.21/1.00  --prep_def_merge_mbd                    true
% 2.21/1.00  --prep_def_merge_tr_red                 false
% 2.21/1.00  --prep_def_merge_tr_cl                  false
% 2.21/1.00  --smt_preprocessing                     true
% 2.21/1.00  --smt_ac_axioms                         fast
% 2.21/1.00  --preprocessed_out                      false
% 2.21/1.00  --preprocessed_stats                    false
% 2.21/1.00  
% 2.21/1.00  ------ Abstraction refinement Options
% 2.21/1.00  
% 2.21/1.00  --abstr_ref                             []
% 2.21/1.00  --abstr_ref_prep                        false
% 2.21/1.00  --abstr_ref_until_sat                   false
% 2.21/1.00  --abstr_ref_sig_restrict                funpre
% 2.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.00  --abstr_ref_under                       []
% 2.21/1.00  
% 2.21/1.00  ------ SAT Options
% 2.21/1.00  
% 2.21/1.00  --sat_mode                              false
% 2.21/1.00  --sat_fm_restart_options                ""
% 2.21/1.00  --sat_gr_def                            false
% 2.21/1.00  --sat_epr_types                         true
% 2.21/1.00  --sat_non_cyclic_types                  false
% 2.21/1.00  --sat_finite_models                     false
% 2.21/1.00  --sat_fm_lemmas                         false
% 2.21/1.00  --sat_fm_prep                           false
% 2.21/1.00  --sat_fm_uc_incr                        true
% 2.21/1.00  --sat_out_model                         small
% 2.21/1.00  --sat_out_clauses                       false
% 2.21/1.00  
% 2.21/1.00  ------ QBF Options
% 2.21/1.00  
% 2.21/1.00  --qbf_mode                              false
% 2.21/1.00  --qbf_elim_univ                         false
% 2.21/1.00  --qbf_dom_inst                          none
% 2.21/1.00  --qbf_dom_pre_inst                      false
% 2.21/1.00  --qbf_sk_in                             false
% 2.21/1.00  --qbf_pred_elim                         true
% 2.21/1.00  --qbf_split                             512
% 2.21/1.00  
% 2.21/1.00  ------ BMC1 Options
% 2.21/1.00  
% 2.21/1.00  --bmc1_incremental                      false
% 2.21/1.00  --bmc1_axioms                           reachable_all
% 2.21/1.00  --bmc1_min_bound                        0
% 2.21/1.00  --bmc1_max_bound                        -1
% 2.21/1.00  --bmc1_max_bound_default                -1
% 2.21/1.00  --bmc1_symbol_reachability              true
% 2.21/1.00  --bmc1_property_lemmas                  false
% 2.21/1.00  --bmc1_k_induction                      false
% 2.21/1.00  --bmc1_non_equiv_states                 false
% 2.21/1.00  --bmc1_deadlock                         false
% 2.21/1.00  --bmc1_ucm                              false
% 2.21/1.00  --bmc1_add_unsat_core                   none
% 2.21/1.00  --bmc1_unsat_core_children              false
% 2.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.00  --bmc1_out_stat                         full
% 2.21/1.00  --bmc1_ground_init                      false
% 2.21/1.00  --bmc1_pre_inst_next_state              false
% 2.21/1.00  --bmc1_pre_inst_state                   false
% 2.21/1.00  --bmc1_pre_inst_reach_state             false
% 2.21/1.00  --bmc1_out_unsat_core                   false
% 2.21/1.00  --bmc1_aig_witness_out                  false
% 2.21/1.00  --bmc1_verbose                          false
% 2.21/1.00  --bmc1_dump_clauses_tptp                false
% 2.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.00  --bmc1_dump_file                        -
% 2.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.00  --bmc1_ucm_extend_mode                  1
% 2.21/1.00  --bmc1_ucm_init_mode                    2
% 2.21/1.00  --bmc1_ucm_cone_mode                    none
% 2.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.00  --bmc1_ucm_relax_model                  4
% 2.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.00  --bmc1_ucm_layered_model                none
% 2.21/1.00  --bmc1_ucm_max_lemma_size               10
% 2.21/1.00  
% 2.21/1.00  ------ AIG Options
% 2.21/1.00  
% 2.21/1.00  --aig_mode                              false
% 2.21/1.00  
% 2.21/1.00  ------ Instantiation Options
% 2.21/1.00  
% 2.21/1.00  --instantiation_flag                    true
% 2.21/1.00  --inst_sos_flag                         false
% 2.21/1.00  --inst_sos_phase                        true
% 2.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.00  --inst_lit_sel_side                     none
% 2.21/1.00  --inst_solver_per_active                1400
% 2.21/1.00  --inst_solver_calls_frac                1.
% 2.21/1.00  --inst_passive_queue_type               priority_queues
% 2.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.00  --inst_passive_queues_freq              [25;2]
% 2.21/1.00  --inst_dismatching                      true
% 2.21/1.00  --inst_eager_unprocessed_to_passive     true
% 2.21/1.00  --inst_prop_sim_given                   true
% 2.21/1.00  --inst_prop_sim_new                     false
% 2.21/1.00  --inst_subs_new                         false
% 2.21/1.00  --inst_eq_res_simp                      false
% 2.21/1.00  --inst_subs_given                       false
% 2.21/1.00  --inst_orphan_elimination               true
% 2.21/1.00  --inst_learning_loop_flag               true
% 2.21/1.00  --inst_learning_start                   3000
% 2.21/1.00  --inst_learning_factor                  2
% 2.21/1.00  --inst_start_prop_sim_after_learn       3
% 2.21/1.00  --inst_sel_renew                        solver
% 2.21/1.00  --inst_lit_activity_flag                true
% 2.21/1.00  --inst_restr_to_given                   false
% 2.21/1.00  --inst_activity_threshold               500
% 2.21/1.00  --inst_out_proof                        true
% 2.21/1.00  
% 2.21/1.00  ------ Resolution Options
% 2.21/1.00  
% 2.21/1.00  --resolution_flag                       false
% 2.21/1.00  --res_lit_sel                           adaptive
% 2.21/1.00  --res_lit_sel_side                      none
% 2.21/1.00  --res_ordering                          kbo
% 2.21/1.00  --res_to_prop_solver                    active
% 2.21/1.00  --res_prop_simpl_new                    false
% 2.21/1.00  --res_prop_simpl_given                  true
% 2.21/1.00  --res_passive_queue_type                priority_queues
% 2.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.00  --res_passive_queues_freq               [15;5]
% 2.21/1.00  --res_forward_subs                      full
% 2.21/1.00  --res_backward_subs                     full
% 2.21/1.00  --res_forward_subs_resolution           true
% 2.21/1.00  --res_backward_subs_resolution          true
% 2.21/1.00  --res_orphan_elimination                true
% 2.21/1.00  --res_time_limit                        2.
% 2.21/1.00  --res_out_proof                         true
% 2.21/1.00  
% 2.21/1.00  ------ Superposition Options
% 2.21/1.00  
% 2.21/1.00  --superposition_flag                    true
% 2.21/1.00  --sup_passive_queue_type                priority_queues
% 2.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.00  --demod_completeness_check              fast
% 2.21/1.00  --demod_use_ground                      true
% 2.21/1.00  --sup_to_prop_solver                    passive
% 2.21/1.00  --sup_prop_simpl_new                    true
% 2.21/1.00  --sup_prop_simpl_given                  true
% 2.21/1.00  --sup_fun_splitting                     false
% 2.21/1.00  --sup_smt_interval                      50000
% 2.21/1.00  
% 2.21/1.00  ------ Superposition Simplification Setup
% 2.21/1.00  
% 2.21/1.00  --sup_indices_passive                   []
% 2.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_full_bw                           [BwDemod]
% 2.21/1.00  --sup_immed_triv                        [TrivRules]
% 2.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_immed_bw_main                     []
% 2.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.00  
% 2.21/1.00  ------ Combination Options
% 2.21/1.00  
% 2.21/1.00  --comb_res_mult                         3
% 2.21/1.00  --comb_sup_mult                         2
% 2.21/1.00  --comb_inst_mult                        10
% 2.21/1.00  
% 2.21/1.00  ------ Debug Options
% 2.21/1.00  
% 2.21/1.00  --dbg_backtrace                         false
% 2.21/1.00  --dbg_dump_prop_clauses                 false
% 2.21/1.00  --dbg_dump_prop_clauses_file            -
% 2.21/1.00  --dbg_out_stat                          false
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  ------ Proving...
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  % SZS status Theorem for theBenchmark.p
% 2.21/1.00  
% 2.21/1.00   Resolution empty clause
% 2.21/1.00  
% 2.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.00  
% 2.21/1.00  fof(f4,axiom,(
% 2.21/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f11,plain,(
% 2.21/1.00    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/1.00    inference(ennf_transformation,[],[f4])).
% 2.21/1.00  
% 2.21/1.00  fof(f12,plain,(
% 2.21/1.00    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(flattening,[],[f11])).
% 2.21/1.00  
% 2.21/1.00  fof(f16,plain,(
% 2.21/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(nnf_transformation,[],[f12])).
% 2.21/1.00  
% 2.21/1.00  fof(f17,plain,(
% 2.21/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(rectify,[],[f16])).
% 2.21/1.00  
% 2.21/1.00  fof(f18,plain,(
% 2.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1))) & r2_hidden(sK0(X0,X1),k1_relat_1(X1))))),
% 2.21/1.00    introduced(choice_axiom,[])).
% 2.21/1.00  
% 2.21/1.00  fof(f19,plain,(
% 2.21/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1))) & r2_hidden(sK0(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 2.21/1.00  
% 2.21/1.00  fof(f30,plain,(
% 2.21/1.00    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK0(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.00    inference(cnf_transformation,[],[f19])).
% 2.21/1.00  
% 2.21/1.00  fof(f6,axiom,(
% 2.21/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f13,plain,(
% 2.21/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.21/1.00    inference(ennf_transformation,[],[f6])).
% 2.21/1.00  
% 2.21/1.00  fof(f20,plain,(
% 2.21/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 2.21/1.00    introduced(choice_axiom,[])).
% 2.21/1.00  
% 2.21/1.00  fof(f21,plain,(
% 2.21/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)))),
% 2.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 2.21/1.00  
% 2.21/1.00  fof(f37,plain,(
% 2.21/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 2.21/1.00    inference(cnf_transformation,[],[f21])).
% 2.21/1.00  
% 2.21/1.00  fof(f7,conjecture,(
% 2.21/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f8,negated_conjecture,(
% 2.21/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 2.21/1.00    inference(negated_conjecture,[],[f7])).
% 2.21/1.00  
% 2.21/1.00  fof(f14,plain,(
% 2.21/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.21/1.00    inference(ennf_transformation,[],[f8])).
% 2.21/1.00  
% 2.21/1.00  fof(f15,plain,(
% 2.21/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.21/1.00    inference(flattening,[],[f14])).
% 2.21/1.00  
% 2.21/1.00  fof(f22,plain,(
% 2.21/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.21/1.00    introduced(choice_axiom,[])).
% 2.21/1.00  
% 2.21/1.00  fof(f23,plain,(
% 2.21/1.00    ~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 2.21/1.00  
% 2.21/1.00  fof(f40,plain,(
% 2.21/1.00    ~v5_funct_1(k1_xboole_0,sK2)),
% 2.21/1.00    inference(cnf_transformation,[],[f23])).
% 2.21/1.00  
% 2.21/1.00  fof(f1,axiom,(
% 2.21/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f24,plain,(
% 2.21/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/1.00    inference(cnf_transformation,[],[f1])).
% 2.21/1.00  
% 2.21/1.00  fof(f36,plain,(
% 2.21/1.00    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0) )),
% 2.21/1.00    inference(cnf_transformation,[],[f21])).
% 2.21/1.00  
% 2.21/1.00  fof(f2,axiom,(
% 2.21/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f9,plain,(
% 2.21/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(ennf_transformation,[],[f2])).
% 2.21/1.00  
% 2.21/1.00  fof(f10,plain,(
% 2.21/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.21/1.00    inference(flattening,[],[f9])).
% 2.21/1.00  
% 2.21/1.00  fof(f26,plain,(
% 2.21/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.00    inference(cnf_transformation,[],[f10])).
% 2.21/1.00  
% 2.21/1.00  fof(f34,plain,(
% 2.21/1.00    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1))) )),
% 2.21/1.00    inference(cnf_transformation,[],[f21])).
% 2.21/1.00  
% 2.21/1.00  fof(f38,plain,(
% 2.21/1.00    v1_relat_1(sK2)),
% 2.21/1.00    inference(cnf_transformation,[],[f23])).
% 2.21/1.00  
% 2.21/1.00  fof(f39,plain,(
% 2.21/1.00    v1_funct_1(sK2)),
% 2.21/1.00    inference(cnf_transformation,[],[f23])).
% 2.21/1.00  
% 2.21/1.00  fof(f5,axiom,(
% 2.21/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f33,plain,(
% 2.21/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.21/1.00    inference(cnf_transformation,[],[f5])).
% 2.21/1.00  
% 2.21/1.00  fof(f3,axiom,(
% 2.21/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.00  
% 2.21/1.00  fof(f28,plain,(
% 2.21/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.21/1.00    inference(cnf_transformation,[],[f3])).
% 2.21/1.00  
% 2.21/1.00  fof(f32,plain,(
% 2.21/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.21/1.00    inference(cnf_transformation,[],[f5])).
% 2.21/1.00  
% 2.21/1.00  fof(f31,plain,(
% 2.21/1.00    ( ! [X0,X1] : (v5_funct_1(X1,X0) | ~r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.00    inference(cnf_transformation,[],[f19])).
% 2.21/1.00  
% 2.21/1.00  cnf(c_6,plain,
% 2.21/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X1))
% 2.21/1.00      | v5_funct_1(X1,X0)
% 2.21/1.00      | ~ v1_funct_1(X1)
% 2.21/1.00      | ~ v1_funct_1(X0)
% 2.21/1.00      | ~ v1_relat_1(X0)
% 2.21/1.00      | ~ v1_relat_1(X1) ),
% 2.21/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_528,plain,
% 2.21/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X1)) = iProver_top
% 2.21/1.00      | v5_funct_1(X1,X0) = iProver_top
% 2.21/1.00      | v1_funct_1(X1) != iProver_top
% 2.21/1.00      | v1_funct_1(X0) != iProver_top
% 2.21/1.00      | v1_relat_1(X1) != iProver_top
% 2.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_10,plain,
% 2.21/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK1(X1,X2),X0) = X2 ),
% 2.21/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_524,plain,
% 2.21/1.00      ( k1_funct_1(sK1(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1440,plain,
% 2.21/1.00      ( k1_funct_1(sK1(k1_relat_1(X0),X1),sK0(X2,X0)) = X1
% 2.21/1.00      | v5_funct_1(X0,X2) = iProver_top
% 2.21/1.00      | v1_funct_1(X2) != iProver_top
% 2.21/1.00      | v1_funct_1(X0) != iProver_top
% 2.21/1.00      | v1_relat_1(X2) != iProver_top
% 2.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_528,c_524]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_14,negated_conjecture,
% 2.21/1.00      ( ~ v5_funct_1(k1_xboole_0,sK2) ),
% 2.21/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_521,plain,
% 2.21/1.00      ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1561,plain,
% 2.21/1.00      ( k1_funct_1(sK1(k1_relat_1(k1_xboole_0),X0),sK0(sK2,k1_xboole_0)) = X0
% 2.21/1.00      | v1_funct_1(sK2) != iProver_top
% 2.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.21/1.00      | v1_relat_1(sK2) != iProver_top
% 2.21/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1440,c_521]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1,plain,
% 2.21/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f24]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_11,plain,
% 2.21/1.00      ( k1_relat_1(sK1(X0,X1)) = X0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_3,plain,
% 2.21/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_530,plain,
% 2.21/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.21/1.00      | k1_xboole_0 = X0
% 2.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1187,plain,
% 2.21/1.00      ( sK1(X0,X1) = k1_xboole_0
% 2.21/1.00      | k1_xboole_0 != X0
% 2.21/1.00      | v1_relat_1(sK1(X0,X1)) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_11,c_530]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_13,plain,
% 2.21/1.00      ( v1_relat_1(sK1(X0,X1)) ),
% 2.21/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_20,plain,
% 2.21/1.00      ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1285,plain,
% 2.21/1.00      ( k1_xboole_0 != X0 | sK1(X0,X1) = k1_xboole_0 ),
% 2.21/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1187,c_20]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1286,plain,
% 2.21/1.00      ( sK1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.21/1.00      inference(renaming,[status(thm)],[c_1285]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1290,plain,
% 2.21/1.00      ( sK1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.21/1.00      inference(equality_resolution,[status(thm)],[c_1286]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1562,plain,
% 2.21/1.00      ( k1_funct_1(k1_xboole_0,sK0(sK2,k1_xboole_0)) = X0
% 2.21/1.00      | v1_funct_1(sK2) != iProver_top
% 2.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.21/1.00      | v1_relat_1(sK2) != iProver_top
% 2.21/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.00      inference(light_normalisation,[status(thm)],[c_1561,c_1,c_1290]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_16,negated_conjecture,
% 2.21/1.00      ( v1_relat_1(sK2) ),
% 2.21/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_17,plain,
% 2.21/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_15,negated_conjecture,
% 2.21/1.00      ( v1_funct_1(sK2) ),
% 2.21/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_18,plain,
% 2.21/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_8,plain,
% 2.21/1.00      ( v1_funct_1(k6_relat_1(X0)) ),
% 2.21/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_33,plain,
% 2.21/1.00      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_35,plain,
% 2.21/1.00      ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4,plain,
% 2.21/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_263,plain,( X0 = X0 ),theory(equality) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_282,plain,
% 2.21/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_272,plain,
% 2.21/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.21/1.00      theory(equality) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_657,plain,
% 2.21/1.00      ( v1_funct_1(X0) | ~ v1_funct_1(k6_relat_1(X1)) | X0 != k6_relat_1(X1) ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_272]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_658,plain,
% 2.21/1.00      ( X0 != k6_relat_1(X1)
% 2.21/1.00      | v1_funct_1(X0) = iProver_top
% 2.21/1.00      | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_660,plain,
% 2.21/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 2.21/1.00      | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 2.21/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_658]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_9,plain,
% 2.21/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.21/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_525,plain,
% 2.21/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_825,plain,
% 2.21/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_4,c_525]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_264,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_905,plain,
% 2.21/1.00      ( X0 != X1 | X0 = k6_relat_1(X2) | k6_relat_1(X2) != X1 ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_264]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_906,plain,
% 2.21/1.00      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 2.21/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 2.21/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_905]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1567,plain,
% 2.21/1.00      ( k1_funct_1(k1_xboole_0,sK0(sK2,k1_xboole_0)) = X0 ),
% 2.21/1.00      inference(global_propositional_subsumption,
% 2.21/1.00                [status(thm)],
% 2.21/1.00                [c_1562,c_17,c_18,c_35,c_4,c_282,c_660,c_825,c_906]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1578,plain,
% 2.21/1.00      ( X0 = X1 ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1567,c_1567]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_5,plain,
% 2.21/1.00      ( ~ r2_hidden(k1_funct_1(X0,sK0(X1,X0)),k1_funct_1(X1,sK0(X1,X0)))
% 2.21/1.00      | v5_funct_1(X0,X1)
% 2.21/1.00      | ~ v1_funct_1(X0)
% 2.21/1.00      | ~ v1_funct_1(X1)
% 2.21/1.00      | ~ v1_relat_1(X1)
% 2.21/1.00      | ~ v1_relat_1(X0) ),
% 2.21/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_529,plain,
% 2.21/1.00      ( r2_hidden(k1_funct_1(X0,sK0(X1,X0)),k1_funct_1(X1,sK0(X1,X0))) != iProver_top
% 2.21/1.00      | v5_funct_1(X0,X1) = iProver_top
% 2.21/1.00      | v1_funct_1(X1) != iProver_top
% 2.21/1.00      | v1_funct_1(X0) != iProver_top
% 2.21/1.00      | v1_relat_1(X1) != iProver_top
% 2.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1575,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top
% 2.21/1.00      | v5_funct_1(k1_xboole_0,sK2) = iProver_top
% 2.21/1.00      | v1_funct_1(sK2) != iProver_top
% 2.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.21/1.00      | v1_relat_1(sK2) != iProver_top
% 2.21/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1567,c_529]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1933,plain,
% 2.21/1.00      ( v1_relat_1(X0) = iProver_top ),
% 2.21/1.00      inference(demodulation,[status(thm)],[c_1578,c_525]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_526,plain,
% 2.21/1.00      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1932,plain,
% 2.21/1.00      ( v1_funct_1(X0) = iProver_top ),
% 2.21/1.00      inference(demodulation,[status(thm)],[c_1578,c_526]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2121,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top
% 2.21/1.00      | v5_funct_1(k1_xboole_0,sK2) = iProver_top ),
% 2.21/1.00      inference(forward_subsumption_resolution,
% 2.21/1.00                [status(thm)],
% 2.21/1.00                [c_1575,c_1933,c_1933,c_1932,c_1932]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_19,plain,
% 2.21/1.00      ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2510,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_funct_1(sK2,sK0(sK2,k1_xboole_0))) != iProver_top ),
% 2.21/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2121,c_19]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2517,plain,
% 2.21/1.00      ( r2_hidden(X0,X1) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1578,c_2510]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1922,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top
% 2.21/1.00      | v5_funct_1(X0,X1) = iProver_top
% 2.21/1.00      | v1_funct_1(X0) != iProver_top
% 2.21/1.00      | v1_funct_1(X1) != iProver_top
% 2.21/1.00      | v1_relat_1(X0) != iProver_top
% 2.21/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.21/1.00      inference(demodulation,[status(thm)],[c_1578,c_528]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1995,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top
% 2.21/1.00      | v5_funct_1(X0,X1) = iProver_top ),
% 2.21/1.00      inference(forward_subsumption_resolution,
% 2.21/1.00                [status(thm)],
% 2.21/1.00                [c_1922,c_1933,c_1933,c_1932,c_1932]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2195,plain,
% 2.21/1.00      ( v5_funct_1(k1_xboole_0,X0) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1578,c_521]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2218,plain,
% 2.21/1.00      ( v5_funct_1(X0,X1) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1578,c_2195]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2714,plain,
% 2.21/1.00      ( r2_hidden(X0,k1_relat_1(X0)) = iProver_top ),
% 2.21/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1995,c_2218]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2732,plain,
% 2.21/1.00      ( $false ),
% 2.21/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2517,c_2714]) ).
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.00  
% 2.21/1.00  ------                               Statistics
% 2.21/1.00  
% 2.21/1.00  ------ General
% 2.21/1.00  
% 2.21/1.00  abstr_ref_over_cycles:                  0
% 2.21/1.00  abstr_ref_under_cycles:                 0
% 2.21/1.00  gc_basic_clause_elim:                   0
% 2.21/1.00  forced_gc_time:                         0
% 2.21/1.00  parsing_time:                           0.013
% 2.21/1.00  unif_index_cands_time:                  0.
% 2.21/1.00  unif_index_add_time:                    0.
% 2.21/1.00  orderings_time:                         0.
% 2.21/1.00  out_proof_time:                         0.012
% 2.21/1.00  total_time:                             0.137
% 2.21/1.00  num_of_symbols:                         43
% 2.21/1.00  num_of_terms:                           3095
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing
% 2.21/1.00  
% 2.21/1.00  num_of_splits:                          0
% 2.21/1.00  num_of_split_atoms:                     0
% 2.21/1.00  num_of_reused_defs:                     0
% 2.21/1.00  num_eq_ax_congr_red:                    8
% 2.21/1.00  num_of_sem_filtered_clauses:            1
% 2.21/1.00  num_of_subtypes:                        0
% 2.21/1.00  monotx_restored_types:                  0
% 2.21/1.00  sat_num_of_epr_types:                   0
% 2.21/1.00  sat_num_of_non_cyclic_types:            0
% 2.21/1.00  sat_guarded_non_collapsed_types:        0
% 2.21/1.00  num_pure_diseq_elim:                    0
% 2.21/1.00  simp_replaced_by:                       0
% 2.21/1.00  res_preprocessed:                       72
% 2.21/1.00  prep_upred:                             0
% 2.21/1.00  prep_unflattend:                        8
% 2.21/1.00  smt_new_axioms:                         0
% 2.21/1.00  pred_elim_cands:                        4
% 2.21/1.00  pred_elim:                              0
% 2.21/1.00  pred_elim_cl:                           0
% 2.21/1.00  pred_elim_cycles:                       1
% 2.21/1.00  merged_defs:                            0
% 2.21/1.00  merged_defs_ncl:                        0
% 2.21/1.00  bin_hyper_res:                          0
% 2.21/1.00  prep_cycles:                            3
% 2.21/1.00  pred_elim_time:                         0.002
% 2.21/1.00  splitting_time:                         0.
% 2.21/1.00  sem_filter_time:                        0.
% 2.21/1.00  monotx_time:                            0.
% 2.21/1.00  subtype_inf_time:                       0.
% 2.21/1.00  
% 2.21/1.00  ------ Problem properties
% 2.21/1.00  
% 2.21/1.00  clauses:                                17
% 2.21/1.00  conjectures:                            3
% 2.21/1.00  epr:                                    3
% 2.21/1.00  horn:                                   16
% 2.21/1.00  ground:                                 6
% 2.21/1.00  unary:                                  11
% 2.21/1.00  binary:                                 1
% 2.21/1.00  lits:                                   38
% 2.21/1.00  lits_eq:                                9
% 2.21/1.00  fd_pure:                                0
% 2.21/1.00  fd_pseudo:                              0
% 2.21/1.00  fd_cond:                                2
% 2.21/1.00  fd_pseudo_cond:                         0
% 2.21/1.00  ac_symbols:                             0
% 2.21/1.00  
% 2.21/1.00  ------ Propositional Solver
% 2.21/1.00  
% 2.21/1.00  prop_solver_calls:                      23
% 2.21/1.00  prop_fast_solver_calls:                 480
% 2.21/1.00  smt_solver_calls:                       0
% 2.21/1.00  smt_fast_solver_calls:                  0
% 2.21/1.00  prop_num_of_clauses:                    981
% 2.21/1.00  prop_preprocess_simplified:             2876
% 2.21/1.00  prop_fo_subsumed:                       16
% 2.21/1.00  prop_solver_time:                       0.
% 2.21/1.00  smt_solver_time:                        0.
% 2.21/1.00  smt_fast_solver_time:                   0.
% 2.21/1.00  prop_fast_solver_time:                  0.
% 2.21/1.00  prop_unsat_core_time:                   0.
% 2.21/1.00  
% 2.21/1.00  ------ QBF
% 2.21/1.00  
% 2.21/1.00  qbf_q_res:                              0
% 2.21/1.00  qbf_num_tautologies:                    0
% 2.21/1.00  qbf_prep_cycles:                        0
% 2.21/1.00  
% 2.21/1.00  ------ BMC1
% 2.21/1.00  
% 2.21/1.00  bmc1_current_bound:                     -1
% 2.21/1.00  bmc1_last_solved_bound:                 -1
% 2.21/1.00  bmc1_unsat_core_size:                   -1
% 2.21/1.00  bmc1_unsat_core_parents_size:           -1
% 2.21/1.00  bmc1_merge_next_fun:                    0
% 2.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.00  
% 2.21/1.00  ------ Instantiation
% 2.21/1.00  
% 2.21/1.00  inst_num_of_clauses:                    254
% 2.21/1.00  inst_num_in_passive:                    111
% 2.21/1.00  inst_num_in_active:                     135
% 2.21/1.00  inst_num_in_unprocessed:                8
% 2.21/1.00  inst_num_of_loops:                      180
% 2.21/1.00  inst_num_of_learning_restarts:          0
% 2.21/1.00  inst_num_moves_active_passive:          42
% 2.21/1.00  inst_lit_activity:                      0
% 2.21/1.00  inst_lit_activity_moves:                0
% 2.21/1.00  inst_num_tautologies:                   0
% 2.21/1.00  inst_num_prop_implied:                  0
% 2.21/1.00  inst_num_existing_simplified:           0
% 2.21/1.00  inst_num_eq_res_simplified:             0
% 2.21/1.00  inst_num_child_elim:                    0
% 2.21/1.00  inst_num_of_dismatching_blockings:      67
% 2.21/1.00  inst_num_of_non_proper_insts:           185
% 2.21/1.00  inst_num_of_duplicates:                 0
% 2.21/1.00  inst_inst_num_from_inst_to_res:         0
% 2.21/1.00  inst_dismatching_checking_time:         0.
% 2.21/1.00  
% 2.21/1.00  ------ Resolution
% 2.21/1.00  
% 2.21/1.00  res_num_of_clauses:                     0
% 2.21/1.00  res_num_in_passive:                     0
% 2.21/1.00  res_num_in_active:                      0
% 2.21/1.00  res_num_of_loops:                       75
% 2.21/1.00  res_forward_subset_subsumed:            6
% 2.21/1.00  res_backward_subset_subsumed:           0
% 2.21/1.00  res_forward_subsumed:                   0
% 2.21/1.00  res_backward_subsumed:                  0
% 2.21/1.00  res_forward_subsumption_resolution:     0
% 2.21/1.00  res_backward_subsumption_resolution:    0
% 2.21/1.00  res_clause_to_clause_subsumption:       244
% 2.21/1.00  res_orphan_elimination:                 0
% 2.21/1.00  res_tautology_del:                      1
% 2.21/1.00  res_num_eq_res_simplified:              0
% 2.21/1.00  res_num_sel_changes:                    0
% 2.21/1.00  res_moves_from_active_to_pass:          0
% 2.21/1.00  
% 2.21/1.00  ------ Superposition
% 2.21/1.00  
% 2.21/1.00  sup_time_total:                         0.
% 2.21/1.00  sup_time_generating:                    0.
% 2.21/1.00  sup_time_sim_full:                      0.
% 2.21/1.00  sup_time_sim_immed:                     0.
% 2.21/1.00  
% 2.21/1.00  sup_num_of_clauses:                     35
% 2.21/1.00  sup_num_in_active:                      16
% 2.21/1.00  sup_num_in_passive:                     19
% 2.21/1.00  sup_num_of_loops:                       34
% 2.21/1.00  sup_fw_superposition:                   29
% 2.21/1.00  sup_bw_superposition:                   61
% 2.21/1.00  sup_immediate_simplified:               40
% 2.21/1.00  sup_given_eliminated:                   3
% 2.21/1.00  comparisons_done:                       0
% 2.21/1.00  comparisons_avoided:                    0
% 2.21/1.00  
% 2.21/1.00  ------ Simplifications
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  sim_fw_subset_subsumed:                 4
% 2.21/1.00  sim_bw_subset_subsumed:                 0
% 2.21/1.00  sim_fw_subsumed:                        15
% 2.21/1.00  sim_bw_subsumed:                        11
% 2.21/1.00  sim_fw_subsumption_res:                 66
% 2.21/1.00  sim_bw_subsumption_res:                 4
% 2.21/1.00  sim_tautology_del:                      2
% 2.21/1.00  sim_eq_tautology_del:                   2
% 2.21/1.00  sim_eq_res_simp:                        0
% 2.21/1.00  sim_fw_demodulated:                     2
% 2.21/1.00  sim_bw_demodulated:                     26
% 2.21/1.00  sim_light_normalised:                   4
% 2.21/1.00  sim_joinable_taut:                      0
% 2.21/1.00  sim_joinable_simp:                      0
% 2.21/1.00  sim_ac_normalised:                      0
% 2.21/1.00  sim_smt_subsumption:                    0
% 2.21/1.00  
%------------------------------------------------------------------------------
