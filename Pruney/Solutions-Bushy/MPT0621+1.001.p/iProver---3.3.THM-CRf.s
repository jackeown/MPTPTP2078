%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0621+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:44 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 178 expanded)
%              Number of clauses        :   45 (  60 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   20
%              Number of atoms          :  267 ( 620 expanded)
%              Number of equality atoms :  149 ( 308 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f20])).

fof(f32,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0] :
      ( o_0_0_xboole_0 = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f18])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f39,f26])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK2(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK2(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f22])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f24])).

fof(f40,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK3
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X2,X0] :
      ( k1_funct_1(sK2(X0),X2) = np__1
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f41,f26])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK1(X1),X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_145,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_146,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_158,plain,
    ( r2_hidden(sK0(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_146,c_12])).

cnf(c_197,plain,
    ( X0 != X1
    | k1_funct_1(sK1(X1),X2) = o_0_0_xboole_0
    | sK0(X0) != X2
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_158])).

cnf(c_198,plain,
    ( k1_funct_1(sK1(X0),sK0(X0)) = o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_3,plain,
    ( k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_377,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_651,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_377])).

cnf(c_9,plain,
    ( v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_25,plain,
    ( v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_28,plain,
    ( v1_funct_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_758,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_25,c_28])).

cnf(c_759,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_758])).

cnf(c_769,plain,
    ( sK2(X0) = sK1(X1)
    | sK3 != X1
    | sK3 != X0
    | v1_relat_1(sK1(X1)) != iProver_top
    | v1_funct_1(sK1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_759])).

cnf(c_5,plain,
    ( v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_380,plain,
    ( v1_relat_1(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_803,plain,
    ( sK2(X0) = sK1(X1)
    | sK3 != X0
    | sK3 != X1
    | v1_funct_1(sK1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_769,c_380])).

cnf(c_807,plain,
    ( sK1(X0) = sK2(sK3)
    | sK3 != X0
    | v1_funct_1(sK1(X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_803])).

cnf(c_4,plain,
    ( v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_38,plain,
    ( v1_funct_1(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_981,plain,
    ( sK3 != X0
    | sK1(X0) = sK2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_38])).

cnf(c_982,plain,
    ( sK1(X0) = sK2(sK3)
    | sK3 != X0 ),
    inference(renaming,[status(thm)],[c_981])).

cnf(c_986,plain,
    ( sK2(sK3) = sK1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_982])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK2(X1),X0) = np__1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_188,plain,
    ( X0 != X1
    | k1_funct_1(sK2(X1),X2) = np__1
    | sK0(X0) != X2
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_158])).

cnf(c_189,plain,
    ( k1_funct_1(sK2(X0),sK0(X0)) = np__1
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_998,plain,
    ( k1_funct_1(sK1(sK3),sK0(sK3)) = np__1
    | sK3 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_986,c_189])).

cnf(c_13,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_264,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_479,plain,
    ( sK3 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_480,plain,
    ( sK3 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_1226,plain,
    ( k1_funct_1(sK1(sK3),sK0(sK3)) = np__1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_13,c_19,c_0,c_480])).

cnf(c_1229,plain,
    ( sK3 = o_0_0_xboole_0
    | np__1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_198,c_1226])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_169,plain,
    ( np__1 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1229,c_480,c_169,c_0,c_19,c_13])).


%------------------------------------------------------------------------------
