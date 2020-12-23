%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:10 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   82 (  95 expanded)
%              Number of clauses        :   48 (  48 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   15
%              Number of atoms          :  220 ( 264 expanded)
%              Number of equality atoms :   76 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f38,plain,(
    ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_5,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_451,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_8,plain,
    ( v5_funct_1(X0,X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_448,plain,
    ( v5_funct_1(X0_42,X1_42)
    | r2_hidden(sK1(X1_42,X0_42),k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(X1_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_677,plain,
    ( v5_funct_1(X0_42,X1_42) = iProver_top
    | r2_hidden(sK1(X1_42,X0_42),k1_relat_1(X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_1031,plain,
    ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
    | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_677])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_455,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_476,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_6,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_450,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_464,plain,
    ( ~ v1_funct_1(X0_42)
    | v1_funct_1(X1_42)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_784,plain,
    ( v1_funct_1(X0_42)
    | ~ v1_funct_1(k6_relat_1(X1_42))
    | X0_42 != k6_relat_1(X1_42) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_785,plain,
    ( X0_42 != k6_relat_1(X1_42)
    | v1_funct_1(X0_42) = iProver_top
    | v1_funct_1(k6_relat_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_787,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_465,plain,
    ( ~ v1_relat_1(X0_42)
    | v1_relat_1(X1_42)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_794,plain,
    ( v1_relat_1(X0_42)
    | ~ v1_relat_1(k6_relat_1(X1_42))
    | X0_42 != k6_relat_1(X1_42) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_795,plain,
    ( X0_42 != k6_relat_1(X1_42)
    | v1_relat_1(X0_42) = iProver_top
    | v1_relat_1(k6_relat_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_797,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_456,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_866,plain,
    ( X0_42 != X1_42
    | X0_42 = k6_relat_1(X2_42)
    | k6_relat_1(X2_42) != X1_42 ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_867,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1090,plain,
    ( v1_funct_1(X0_42) != iProver_top
    | v5_funct_1(k1_xboole_0,X0_42) = iProver_top
    | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_20,c_23,c_476,c_450,c_787,c_797,c_867])).

cnf(c_1091,plain,
    ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
    | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_1090])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_43,k1_xboole_0)) ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_685,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_43,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_453,plain,
    ( k3_xboole_0(X0_43,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_704,plain,
    ( r2_hidden(X0_42,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_685,c_453])).

cnf(c_1098,plain,
    ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1091,c_704])).

cnf(c_12,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_444,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_681,plain,
    ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1102,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_681])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1102,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.83/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.83/0.99  
% 0.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/0.99  
% 0.83/0.99  ------  iProver source info
% 0.83/0.99  
% 0.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/0.99  git: non_committed_changes: false
% 0.83/0.99  git: last_make_outside_of_git: false
% 0.83/0.99  
% 0.83/0.99  ------ 
% 0.83/0.99  
% 0.83/0.99  ------ Input Options
% 0.83/0.99  
% 0.83/0.99  --out_options                           all
% 0.83/0.99  --tptp_safe_out                         true
% 0.83/0.99  --problem_path                          ""
% 0.83/0.99  --include_path                          ""
% 0.83/0.99  --clausifier                            res/vclausify_rel
% 0.83/0.99  --clausifier_options                    --mode clausify
% 0.83/0.99  --stdin                                 false
% 0.83/0.99  --stats_out                             all
% 0.83/0.99  
% 0.83/0.99  ------ General Options
% 0.83/0.99  
% 0.83/0.99  --fof                                   false
% 0.83/0.99  --time_out_real                         305.
% 0.83/0.99  --time_out_virtual                      -1.
% 0.83/0.99  --symbol_type_check                     false
% 0.83/0.99  --clausify_out                          false
% 0.83/0.99  --sig_cnt_out                           false
% 0.83/0.99  --trig_cnt_out                          false
% 0.83/0.99  --trig_cnt_out_tolerance                1.
% 0.83/0.99  --trig_cnt_out_sk_spl                   false
% 0.83/0.99  --abstr_cl_out                          false
% 0.83/0.99  
% 0.83/0.99  ------ Global Options
% 0.83/0.99  
% 0.83/0.99  --schedule                              default
% 0.83/0.99  --add_important_lit                     false
% 0.83/0.99  --prop_solver_per_cl                    1000
% 0.83/0.99  --min_unsat_core                        false
% 0.83/0.99  --soft_assumptions                      false
% 0.83/0.99  --soft_lemma_size                       3
% 0.83/0.99  --prop_impl_unit_size                   0
% 0.83/0.99  --prop_impl_unit                        []
% 0.83/0.99  --share_sel_clauses                     true
% 0.83/0.99  --reset_solvers                         false
% 0.83/0.99  --bc_imp_inh                            [conj_cone]
% 0.83/0.99  --conj_cone_tolerance                   3.
% 0.83/0.99  --extra_neg_conj                        none
% 0.83/0.99  --large_theory_mode                     true
% 0.83/0.99  --prolific_symb_bound                   200
% 0.83/0.99  --lt_threshold                          2000
% 0.83/0.99  --clause_weak_htbl                      true
% 0.83/0.99  --gc_record_bc_elim                     false
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing Options
% 0.83/0.99  
% 0.83/0.99  --preprocessing_flag                    true
% 0.83/0.99  --time_out_prep_mult                    0.1
% 0.83/0.99  --splitting_mode                        input
% 0.83/0.99  --splitting_grd                         true
% 0.83/0.99  --splitting_cvd                         false
% 0.83/0.99  --splitting_cvd_svl                     false
% 0.83/0.99  --splitting_nvd                         32
% 0.83/0.99  --sub_typing                            true
% 0.83/0.99  --prep_gs_sim                           true
% 0.83/0.99  --prep_unflatten                        true
% 0.83/0.99  --prep_res_sim                          true
% 0.83/0.99  --prep_upred                            true
% 0.83/0.99  --prep_sem_filter                       exhaustive
% 0.83/0.99  --prep_sem_filter_out                   false
% 0.83/0.99  --pred_elim                             true
% 0.83/0.99  --res_sim_input                         true
% 0.83/0.99  --eq_ax_congr_red                       true
% 0.83/0.99  --pure_diseq_elim                       true
% 0.83/0.99  --brand_transform                       false
% 0.83/0.99  --non_eq_to_eq                          false
% 0.83/0.99  --prep_def_merge                        true
% 0.83/0.99  --prep_def_merge_prop_impl              false
% 0.83/0.99  --prep_def_merge_mbd                    true
% 0.83/0.99  --prep_def_merge_tr_red                 false
% 0.83/0.99  --prep_def_merge_tr_cl                  false
% 0.83/0.99  --smt_preprocessing                     true
% 0.83/0.99  --smt_ac_axioms                         fast
% 0.83/0.99  --preprocessed_out                      false
% 0.83/0.99  --preprocessed_stats                    false
% 0.83/0.99  
% 0.83/0.99  ------ Abstraction refinement Options
% 0.83/0.99  
% 0.83/0.99  --abstr_ref                             []
% 0.83/0.99  --abstr_ref_prep                        false
% 0.83/0.99  --abstr_ref_until_sat                   false
% 0.83/0.99  --abstr_ref_sig_restrict                funpre
% 0.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.99  --abstr_ref_under                       []
% 0.83/0.99  
% 0.83/0.99  ------ SAT Options
% 0.83/0.99  
% 0.83/0.99  --sat_mode                              false
% 0.83/0.99  --sat_fm_restart_options                ""
% 0.83/0.99  --sat_gr_def                            false
% 0.83/0.99  --sat_epr_types                         true
% 0.83/0.99  --sat_non_cyclic_types                  false
% 0.83/0.99  --sat_finite_models                     false
% 0.83/0.99  --sat_fm_lemmas                         false
% 0.83/0.99  --sat_fm_prep                           false
% 0.83/0.99  --sat_fm_uc_incr                        true
% 0.83/0.99  --sat_out_model                         small
% 0.83/0.99  --sat_out_clauses                       false
% 0.83/0.99  
% 0.83/0.99  ------ QBF Options
% 0.83/0.99  
% 0.83/0.99  --qbf_mode                              false
% 0.83/0.99  --qbf_elim_univ                         false
% 0.83/0.99  --qbf_dom_inst                          none
% 0.83/0.99  --qbf_dom_pre_inst                      false
% 0.83/0.99  --qbf_sk_in                             false
% 0.83/0.99  --qbf_pred_elim                         true
% 0.83/0.99  --qbf_split                             512
% 0.83/0.99  
% 0.83/0.99  ------ BMC1 Options
% 0.83/0.99  
% 0.83/0.99  --bmc1_incremental                      false
% 0.83/0.99  --bmc1_axioms                           reachable_all
% 0.83/0.99  --bmc1_min_bound                        0
% 0.83/0.99  --bmc1_max_bound                        -1
% 0.83/0.99  --bmc1_max_bound_default                -1
% 0.83/0.99  --bmc1_symbol_reachability              true
% 0.83/0.99  --bmc1_property_lemmas                  false
% 0.83/0.99  --bmc1_k_induction                      false
% 0.83/0.99  --bmc1_non_equiv_states                 false
% 0.83/0.99  --bmc1_deadlock                         false
% 0.83/0.99  --bmc1_ucm                              false
% 0.83/0.99  --bmc1_add_unsat_core                   none
% 0.83/0.99  --bmc1_unsat_core_children              false
% 0.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.99  --bmc1_out_stat                         full
% 0.83/0.99  --bmc1_ground_init                      false
% 0.83/0.99  --bmc1_pre_inst_next_state              false
% 0.83/0.99  --bmc1_pre_inst_state                   false
% 0.83/0.99  --bmc1_pre_inst_reach_state             false
% 0.83/0.99  --bmc1_out_unsat_core                   false
% 0.83/0.99  --bmc1_aig_witness_out                  false
% 0.83/0.99  --bmc1_verbose                          false
% 0.83/0.99  --bmc1_dump_clauses_tptp                false
% 0.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.99  --bmc1_dump_file                        -
% 0.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.99  --bmc1_ucm_extend_mode                  1
% 0.83/0.99  --bmc1_ucm_init_mode                    2
% 0.83/0.99  --bmc1_ucm_cone_mode                    none
% 0.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.99  --bmc1_ucm_relax_model                  4
% 0.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.99  --bmc1_ucm_layered_model                none
% 0.83/0.99  --bmc1_ucm_max_lemma_size               10
% 0.83/0.99  
% 0.83/0.99  ------ AIG Options
% 0.83/0.99  
% 0.83/0.99  --aig_mode                              false
% 0.83/0.99  
% 0.83/0.99  ------ Instantiation Options
% 0.83/0.99  
% 0.83/0.99  --instantiation_flag                    true
% 0.83/0.99  --inst_sos_flag                         false
% 0.83/0.99  --inst_sos_phase                        true
% 0.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.99  --inst_lit_sel_side                     num_symb
% 0.83/0.99  --inst_solver_per_active                1400
% 0.83/0.99  --inst_solver_calls_frac                1.
% 0.83/0.99  --inst_passive_queue_type               priority_queues
% 0.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.99  --inst_passive_queues_freq              [25;2]
% 0.83/0.99  --inst_dismatching                      true
% 0.83/0.99  --inst_eager_unprocessed_to_passive     true
% 0.83/0.99  --inst_prop_sim_given                   true
% 0.83/0.99  --inst_prop_sim_new                     false
% 0.83/0.99  --inst_subs_new                         false
% 0.83/0.99  --inst_eq_res_simp                      false
% 0.83/0.99  --inst_subs_given                       false
% 0.83/0.99  --inst_orphan_elimination               true
% 0.83/0.99  --inst_learning_loop_flag               true
% 0.83/0.99  --inst_learning_start                   3000
% 0.83/0.99  --inst_learning_factor                  2
% 0.83/0.99  --inst_start_prop_sim_after_learn       3
% 0.83/0.99  --inst_sel_renew                        solver
% 0.83/0.99  --inst_lit_activity_flag                true
% 0.83/0.99  --inst_restr_to_given                   false
% 0.83/0.99  --inst_activity_threshold               500
% 0.83/0.99  --inst_out_proof                        true
% 0.83/0.99  
% 0.83/0.99  ------ Resolution Options
% 0.83/0.99  
% 0.83/0.99  --resolution_flag                       true
% 0.83/0.99  --res_lit_sel                           adaptive
% 0.83/0.99  --res_lit_sel_side                      none
% 0.83/0.99  --res_ordering                          kbo
% 0.83/0.99  --res_to_prop_solver                    active
% 0.83/0.99  --res_prop_simpl_new                    false
% 0.83/0.99  --res_prop_simpl_given                  true
% 0.83/0.99  --res_passive_queue_type                priority_queues
% 0.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.99  --res_passive_queues_freq               [15;5]
% 0.83/0.99  --res_forward_subs                      full
% 0.83/0.99  --res_backward_subs                     full
% 0.83/0.99  --res_forward_subs_resolution           true
% 0.83/0.99  --res_backward_subs_resolution          true
% 0.83/0.99  --res_orphan_elimination                true
% 0.83/0.99  --res_time_limit                        2.
% 0.83/0.99  --res_out_proof                         true
% 0.83/0.99  
% 0.83/0.99  ------ Superposition Options
% 0.83/0.99  
% 0.83/0.99  --superposition_flag                    true
% 0.83/0.99  --sup_passive_queue_type                priority_queues
% 0.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.99  --demod_completeness_check              fast
% 0.83/0.99  --demod_use_ground                      true
% 0.83/0.99  --sup_to_prop_solver                    passive
% 0.83/0.99  --sup_prop_simpl_new                    true
% 0.83/0.99  --sup_prop_simpl_given                  true
% 0.83/0.99  --sup_fun_splitting                     false
% 0.83/0.99  --sup_smt_interval                      50000
% 0.83/0.99  
% 0.83/0.99  ------ Superposition Simplification Setup
% 0.83/0.99  
% 0.83/0.99  --sup_indices_passive                   []
% 0.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_full_bw                           [BwDemod]
% 0.83/0.99  --sup_immed_triv                        [TrivRules]
% 0.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_immed_bw_main                     []
% 0.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.99  
% 0.83/0.99  ------ Combination Options
% 0.83/0.99  
% 0.83/0.99  --comb_res_mult                         3
% 0.83/0.99  --comb_sup_mult                         2
% 0.83/0.99  --comb_inst_mult                        10
% 0.83/0.99  
% 0.83/0.99  ------ Debug Options
% 0.83/0.99  
% 0.83/0.99  --dbg_backtrace                         false
% 0.83/0.99  --dbg_dump_prop_clauses                 false
% 0.83/0.99  --dbg_dump_prop_clauses_file            -
% 0.83/0.99  --dbg_out_stat                          false
% 0.83/0.99  ------ Parsing...
% 0.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.83/0.99  ------ Proving...
% 0.83/0.99  ------ Problem Properties 
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  clauses                                 14
% 0.83/0.99  conjectures                             3
% 0.83/0.99  EPR                                     3
% 0.83/0.99  Horn                                    13
% 0.83/0.99  unary                                   10
% 0.83/0.99  binary                                  1
% 0.83/0.99  lits                                    31
% 0.83/0.99  lits eq                                 4
% 0.83/0.99  fd_pure                                 0
% 0.83/0.99  fd_pseudo                               0
% 0.83/0.99  fd_cond                                 0
% 0.83/0.99  fd_pseudo_cond                          0
% 0.83/0.99  AC symbols                              0
% 0.83/0.99  
% 0.83/0.99  ------ Schedule dynamic 5 is on 
% 0.83/0.99  
% 0.83/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  ------ 
% 0.83/0.99  Current options:
% 0.83/0.99  ------ 
% 0.83/0.99  
% 0.83/0.99  ------ Input Options
% 0.83/0.99  
% 0.83/0.99  --out_options                           all
% 0.83/0.99  --tptp_safe_out                         true
% 0.83/0.99  --problem_path                          ""
% 0.83/0.99  --include_path                          ""
% 0.83/0.99  --clausifier                            res/vclausify_rel
% 0.83/0.99  --clausifier_options                    --mode clausify
% 0.83/0.99  --stdin                                 false
% 0.83/0.99  --stats_out                             all
% 0.83/0.99  
% 0.83/0.99  ------ General Options
% 0.83/0.99  
% 0.83/0.99  --fof                                   false
% 0.83/0.99  --time_out_real                         305.
% 0.83/0.99  --time_out_virtual                      -1.
% 0.83/0.99  --symbol_type_check                     false
% 0.83/0.99  --clausify_out                          false
% 0.83/0.99  --sig_cnt_out                           false
% 0.83/0.99  --trig_cnt_out                          false
% 0.83/0.99  --trig_cnt_out_tolerance                1.
% 0.83/0.99  --trig_cnt_out_sk_spl                   false
% 0.83/0.99  --abstr_cl_out                          false
% 0.83/0.99  
% 0.83/0.99  ------ Global Options
% 0.83/0.99  
% 0.83/0.99  --schedule                              default
% 0.83/0.99  --add_important_lit                     false
% 0.83/0.99  --prop_solver_per_cl                    1000
% 0.83/0.99  --min_unsat_core                        false
% 0.83/0.99  --soft_assumptions                      false
% 0.83/0.99  --soft_lemma_size                       3
% 0.83/0.99  --prop_impl_unit_size                   0
% 0.83/0.99  --prop_impl_unit                        []
% 0.83/0.99  --share_sel_clauses                     true
% 0.83/0.99  --reset_solvers                         false
% 0.83/0.99  --bc_imp_inh                            [conj_cone]
% 0.83/0.99  --conj_cone_tolerance                   3.
% 0.83/0.99  --extra_neg_conj                        none
% 0.83/0.99  --large_theory_mode                     true
% 0.83/0.99  --prolific_symb_bound                   200
% 0.83/0.99  --lt_threshold                          2000
% 0.83/0.99  --clause_weak_htbl                      true
% 0.83/0.99  --gc_record_bc_elim                     false
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing Options
% 0.83/0.99  
% 0.83/0.99  --preprocessing_flag                    true
% 0.83/0.99  --time_out_prep_mult                    0.1
% 0.83/0.99  --splitting_mode                        input
% 0.83/0.99  --splitting_grd                         true
% 0.83/0.99  --splitting_cvd                         false
% 0.83/0.99  --splitting_cvd_svl                     false
% 0.83/0.99  --splitting_nvd                         32
% 0.83/0.99  --sub_typing                            true
% 0.83/0.99  --prep_gs_sim                           true
% 0.83/0.99  --prep_unflatten                        true
% 0.83/0.99  --prep_res_sim                          true
% 0.83/0.99  --prep_upred                            true
% 0.83/0.99  --prep_sem_filter                       exhaustive
% 0.83/0.99  --prep_sem_filter_out                   false
% 0.83/0.99  --pred_elim                             true
% 0.83/0.99  --res_sim_input                         true
% 0.83/0.99  --eq_ax_congr_red                       true
% 0.83/0.99  --pure_diseq_elim                       true
% 0.83/0.99  --brand_transform                       false
% 0.83/0.99  --non_eq_to_eq                          false
% 0.83/0.99  --prep_def_merge                        true
% 0.83/0.99  --prep_def_merge_prop_impl              false
% 0.83/0.99  --prep_def_merge_mbd                    true
% 0.83/0.99  --prep_def_merge_tr_red                 false
% 0.83/0.99  --prep_def_merge_tr_cl                  false
% 0.83/0.99  --smt_preprocessing                     true
% 0.83/0.99  --smt_ac_axioms                         fast
% 0.83/0.99  --preprocessed_out                      false
% 0.83/0.99  --preprocessed_stats                    false
% 0.83/0.99  
% 0.83/0.99  ------ Abstraction refinement Options
% 0.83/0.99  
% 0.83/0.99  --abstr_ref                             []
% 0.83/0.99  --abstr_ref_prep                        false
% 0.83/0.99  --abstr_ref_until_sat                   false
% 0.83/0.99  --abstr_ref_sig_restrict                funpre
% 0.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.99  --abstr_ref_under                       []
% 0.83/0.99  
% 0.83/0.99  ------ SAT Options
% 0.83/0.99  
% 0.83/0.99  --sat_mode                              false
% 0.83/0.99  --sat_fm_restart_options                ""
% 0.83/0.99  --sat_gr_def                            false
% 0.83/0.99  --sat_epr_types                         true
% 0.83/0.99  --sat_non_cyclic_types                  false
% 0.83/0.99  --sat_finite_models                     false
% 0.83/0.99  --sat_fm_lemmas                         false
% 0.83/0.99  --sat_fm_prep                           false
% 0.83/0.99  --sat_fm_uc_incr                        true
% 0.83/0.99  --sat_out_model                         small
% 0.83/0.99  --sat_out_clauses                       false
% 0.83/0.99  
% 0.83/0.99  ------ QBF Options
% 0.83/0.99  
% 0.83/0.99  --qbf_mode                              false
% 0.83/0.99  --qbf_elim_univ                         false
% 0.83/0.99  --qbf_dom_inst                          none
% 0.83/0.99  --qbf_dom_pre_inst                      false
% 0.83/0.99  --qbf_sk_in                             false
% 0.83/0.99  --qbf_pred_elim                         true
% 0.83/0.99  --qbf_split                             512
% 0.83/0.99  
% 0.83/0.99  ------ BMC1 Options
% 0.83/0.99  
% 0.83/0.99  --bmc1_incremental                      false
% 0.83/0.99  --bmc1_axioms                           reachable_all
% 0.83/0.99  --bmc1_min_bound                        0
% 0.83/0.99  --bmc1_max_bound                        -1
% 0.83/0.99  --bmc1_max_bound_default                -1
% 0.83/0.99  --bmc1_symbol_reachability              true
% 0.83/1.00  --bmc1_property_lemmas                  false
% 0.83/1.00  --bmc1_k_induction                      false
% 0.83/1.00  --bmc1_non_equiv_states                 false
% 0.83/1.00  --bmc1_deadlock                         false
% 0.83/1.00  --bmc1_ucm                              false
% 0.83/1.00  --bmc1_add_unsat_core                   none
% 0.83/1.00  --bmc1_unsat_core_children              false
% 0.83/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.00  --bmc1_out_stat                         full
% 0.83/1.00  --bmc1_ground_init                      false
% 0.83/1.00  --bmc1_pre_inst_next_state              false
% 0.83/1.00  --bmc1_pre_inst_state                   false
% 0.83/1.00  --bmc1_pre_inst_reach_state             false
% 0.83/1.00  --bmc1_out_unsat_core                   false
% 0.83/1.00  --bmc1_aig_witness_out                  false
% 0.83/1.00  --bmc1_verbose                          false
% 0.83/1.00  --bmc1_dump_clauses_tptp                false
% 0.83/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.00  --bmc1_dump_file                        -
% 0.83/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.00  --bmc1_ucm_extend_mode                  1
% 0.83/1.00  --bmc1_ucm_init_mode                    2
% 0.83/1.00  --bmc1_ucm_cone_mode                    none
% 0.83/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.00  --bmc1_ucm_relax_model                  4
% 0.83/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.00  --bmc1_ucm_layered_model                none
% 0.83/1.00  --bmc1_ucm_max_lemma_size               10
% 0.83/1.00  
% 0.83/1.00  ------ AIG Options
% 0.83/1.00  
% 0.83/1.00  --aig_mode                              false
% 0.83/1.00  
% 0.83/1.00  ------ Instantiation Options
% 0.83/1.00  
% 0.83/1.00  --instantiation_flag                    true
% 0.83/1.00  --inst_sos_flag                         false
% 0.83/1.00  --inst_sos_phase                        true
% 0.83/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.00  --inst_lit_sel_side                     none
% 0.83/1.00  --inst_solver_per_active                1400
% 0.83/1.00  --inst_solver_calls_frac                1.
% 0.83/1.00  --inst_passive_queue_type               priority_queues
% 0.83/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.00  --inst_passive_queues_freq              [25;2]
% 0.83/1.00  --inst_dismatching                      true
% 0.83/1.00  --inst_eager_unprocessed_to_passive     true
% 0.83/1.00  --inst_prop_sim_given                   true
% 0.83/1.00  --inst_prop_sim_new                     false
% 0.83/1.00  --inst_subs_new                         false
% 0.83/1.00  --inst_eq_res_simp                      false
% 0.83/1.00  --inst_subs_given                       false
% 0.83/1.00  --inst_orphan_elimination               true
% 0.83/1.00  --inst_learning_loop_flag               true
% 0.83/1.00  --inst_learning_start                   3000
% 0.83/1.00  --inst_learning_factor                  2
% 0.83/1.00  --inst_start_prop_sim_after_learn       3
% 0.83/1.00  --inst_sel_renew                        solver
% 0.83/1.00  --inst_lit_activity_flag                true
% 0.83/1.00  --inst_restr_to_given                   false
% 0.83/1.00  --inst_activity_threshold               500
% 0.83/1.00  --inst_out_proof                        true
% 0.83/1.00  
% 0.83/1.00  ------ Resolution Options
% 0.83/1.00  
% 0.83/1.00  --resolution_flag                       false
% 0.83/1.00  --res_lit_sel                           adaptive
% 0.83/1.00  --res_lit_sel_side                      none
% 0.83/1.00  --res_ordering                          kbo
% 0.83/1.00  --res_to_prop_solver                    active
% 0.83/1.00  --res_prop_simpl_new                    false
% 0.83/1.00  --res_prop_simpl_given                  true
% 0.83/1.00  --res_passive_queue_type                priority_queues
% 0.83/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.00  --res_passive_queues_freq               [15;5]
% 0.83/1.00  --res_forward_subs                      full
% 0.83/1.00  --res_backward_subs                     full
% 0.83/1.00  --res_forward_subs_resolution           true
% 0.83/1.00  --res_backward_subs_resolution          true
% 0.83/1.00  --res_orphan_elimination                true
% 0.83/1.00  --res_time_limit                        2.
% 0.83/1.00  --res_out_proof                         true
% 0.83/1.00  
% 0.83/1.00  ------ Superposition Options
% 0.83/1.00  
% 0.83/1.00  --superposition_flag                    true
% 0.83/1.00  --sup_passive_queue_type                priority_queues
% 0.83/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.00  --demod_completeness_check              fast
% 0.83/1.00  --demod_use_ground                      true
% 0.83/1.00  --sup_to_prop_solver                    passive
% 0.83/1.00  --sup_prop_simpl_new                    true
% 0.83/1.00  --sup_prop_simpl_given                  true
% 0.83/1.00  --sup_fun_splitting                     false
% 0.83/1.00  --sup_smt_interval                      50000
% 0.83/1.00  
% 0.83/1.00  ------ Superposition Simplification Setup
% 0.83/1.00  
% 0.83/1.00  --sup_indices_passive                   []
% 0.83/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_full_bw                           [BwDemod]
% 0.83/1.00  --sup_immed_triv                        [TrivRules]
% 0.83/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_immed_bw_main                     []
% 0.83/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.00  
% 0.83/1.00  ------ Combination Options
% 0.83/1.00  
% 0.83/1.00  --comb_res_mult                         3
% 0.83/1.00  --comb_sup_mult                         2
% 0.83/1.00  --comb_inst_mult                        10
% 0.83/1.00  
% 0.83/1.00  ------ Debug Options
% 0.83/1.00  
% 0.83/1.00  --dbg_backtrace                         false
% 0.83/1.00  --dbg_dump_prop_clauses                 false
% 0.83/1.00  --dbg_dump_prop_clauses_file            -
% 0.83/1.00  --dbg_out_stat                          false
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  ------ Proving...
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  % SZS status Theorem for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  fof(f4,axiom,(
% 0.83/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f28,plain,(
% 0.83/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.83/1.00    inference(cnf_transformation,[],[f4])).
% 0.83/1.00  
% 0.83/1.00  fof(f6,axiom,(
% 0.83/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f12,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/1.00    inference(ennf_transformation,[],[f6])).
% 0.83/1.00  
% 0.83/1.00  fof(f13,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(flattening,[],[f12])).
% 0.83/1.00  
% 0.83/1.00  fof(f18,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f13])).
% 0.83/1.00  
% 0.83/1.00  fof(f19,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(rectify,[],[f18])).
% 0.83/1.00  
% 0.83/1.00  fof(f20,plain,(
% 0.83/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f21,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.83/1.00  
% 0.83/1.00  fof(f32,plain,(
% 0.83/1.00    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f21])).
% 0.83/1.00  
% 0.83/1.00  fof(f7,axiom,(
% 0.83/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f34,plain,(
% 0.83/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.83/1.00    inference(cnf_transformation,[],[f7])).
% 0.83/1.00  
% 0.83/1.00  fof(f35,plain,(
% 0.83/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.83/1.00    inference(cnf_transformation,[],[f7])).
% 0.83/1.00  
% 0.83/1.00  fof(f5,axiom,(
% 0.83/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f30,plain,(
% 0.83/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.83/1.00    inference(cnf_transformation,[],[f5])).
% 0.83/1.00  
% 0.83/1.00  fof(f1,axiom,(
% 0.83/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f10,plain,(
% 0.83/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.83/1.00    inference(rectify,[],[f1])).
% 0.83/1.00  
% 0.83/1.00  fof(f11,plain,(
% 0.83/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.83/1.00    inference(ennf_transformation,[],[f10])).
% 0.83/1.00  
% 0.83/1.00  fof(f16,plain,(
% 0.83/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f17,plain,(
% 0.83/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.83/1.00  
% 0.83/1.00  fof(f25,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f3,axiom,(
% 0.83/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f27,plain,(
% 0.83/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f3])).
% 0.83/1.00  
% 0.83/1.00  fof(f2,axiom,(
% 0.83/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f26,plain,(
% 0.83/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 0.83/1.00    inference(cnf_transformation,[],[f2])).
% 0.83/1.00  
% 0.83/1.00  fof(f8,conjecture,(
% 0.83/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f9,negated_conjecture,(
% 0.83/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.83/1.00    inference(negated_conjecture,[],[f8])).
% 0.83/1.00  
% 0.83/1.00  fof(f14,plain,(
% 0.83/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.83/1.00    inference(ennf_transformation,[],[f9])).
% 0.83/1.00  
% 0.83/1.00  fof(f15,plain,(
% 0.83/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.83/1.00    inference(flattening,[],[f14])).
% 0.83/1.00  
% 0.83/1.00  fof(f22,plain,(
% 0.83/1.00    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f23,plain,(
% 0.83/1.00    ~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.83/1.00  
% 0.83/1.00  fof(f38,plain,(
% 0.83/1.00    ~v5_funct_1(k1_xboole_0,sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f23])).
% 0.83/1.00  
% 0.83/1.00  fof(f37,plain,(
% 0.83/1.00    v1_funct_1(sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f23])).
% 0.83/1.00  
% 0.83/1.00  fof(f36,plain,(
% 0.83/1.00    v1_relat_1(sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f23])).
% 0.83/1.00  
% 0.83/1.00  cnf(c_5,plain,
% 0.83/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_451,plain,
% 0.83/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_8,plain,
% 0.83/1.00      ( v5_funct_1(X0,X1)
% 0.83/1.00      | r2_hidden(sK1(X1,X0),k1_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X1)
% 0.83/1.00      | ~ v1_funct_1(X0)
% 0.83/1.00      | ~ v1_funct_1(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_448,plain,
% 0.83/1.00      ( v5_funct_1(X0_42,X1_42)
% 0.83/1.00      | r2_hidden(sK1(X1_42,X0_42),k1_relat_1(X0_42))
% 0.83/1.00      | ~ v1_relat_1(X0_42)
% 0.83/1.00      | ~ v1_relat_1(X1_42)
% 0.83/1.00      | ~ v1_funct_1(X0_42)
% 0.83/1.00      | ~ v1_funct_1(X1_42) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_677,plain,
% 0.83/1.00      ( v5_funct_1(X0_42,X1_42) = iProver_top
% 0.83/1.00      | r2_hidden(sK1(X1_42,X0_42),k1_relat_1(X0_42)) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_42) != iProver_top
% 0.83/1.00      | v1_relat_1(X1_42) != iProver_top
% 0.83/1.00      | v1_funct_1(X0_42) != iProver_top
% 0.83/1.00      | v1_funct_1(X1_42) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1031,plain,
% 0.83/1.00      ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
% 0.83/1.00      | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_42) != iProver_top
% 0.83/1.00      | v1_relat_1(k1_xboole_0) != iProver_top
% 0.83/1.00      | v1_funct_1(X0_42) != iProver_top
% 0.83/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 0.83/1.00      inference(superposition,[status(thm)],[c_451,c_677]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_11,plain,
% 0.83/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 0.83/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_18,plain,
% 0.83/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_20,plain,
% 0.83/1.00      ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_10,plain,
% 0.83/1.00      ( v1_funct_1(k6_relat_1(X0)) ),
% 0.83/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_21,plain,
% 0.83/1.00      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_23,plain,
% 0.83/1.00      ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_455,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_476,plain,
% 0.83/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_455]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_6,plain,
% 0.83/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_450,plain,
% 0.83/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_464,plain,
% 0.83/1.00      ( ~ v1_funct_1(X0_42) | v1_funct_1(X1_42) | X1_42 != X0_42 ),
% 0.83/1.00      theory(equality) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_784,plain,
% 0.83/1.00      ( v1_funct_1(X0_42)
% 0.83/1.00      | ~ v1_funct_1(k6_relat_1(X1_42))
% 0.83/1.00      | X0_42 != k6_relat_1(X1_42) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_464]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_785,plain,
% 0.83/1.00      ( X0_42 != k6_relat_1(X1_42)
% 0.83/1.00      | v1_funct_1(X0_42) = iProver_top
% 0.83/1.00      | v1_funct_1(k6_relat_1(X1_42)) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_787,plain,
% 0.83/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 0.83/1.00      | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 0.83/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_785]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_465,plain,
% 0.83/1.00      ( ~ v1_relat_1(X0_42) | v1_relat_1(X1_42) | X1_42 != X0_42 ),
% 0.83/1.00      theory(equality) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_794,plain,
% 0.83/1.00      ( v1_relat_1(X0_42)
% 0.83/1.00      | ~ v1_relat_1(k6_relat_1(X1_42))
% 0.83/1.00      | X0_42 != k6_relat_1(X1_42) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_465]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_795,plain,
% 0.83/1.00      ( X0_42 != k6_relat_1(X1_42)
% 0.83/1.00      | v1_relat_1(X0_42) = iProver_top
% 0.83/1.00      | v1_relat_1(k6_relat_1(X1_42)) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_797,plain,
% 0.83/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 0.83/1.00      | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 0.83/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_795]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_456,plain,
% 0.83/1.00      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.83/1.00      theory(equality) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_866,plain,
% 0.83/1.00      ( X0_42 != X1_42
% 0.83/1.00      | X0_42 = k6_relat_1(X2_42)
% 0.83/1.00      | k6_relat_1(X2_42) != X1_42 ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_456]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_867,plain,
% 0.83/1.00      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 0.83/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 0.83/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_866]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1090,plain,
% 0.83/1.00      ( v1_funct_1(X0_42) != iProver_top
% 0.83/1.00      | v5_funct_1(k1_xboole_0,X0_42) = iProver_top
% 0.83/1.00      | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_42) != iProver_top ),
% 0.83/1.00      inference(global_propositional_subsumption,
% 0.83/1.00                [status(thm)],
% 0.83/1.00                [c_1031,c_20,c_23,c_476,c_450,c_787,c_797,c_867]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1091,plain,
% 0.83/1.00      ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
% 0.83/1.00      | r2_hidden(sK1(X0_42,k1_xboole_0),k1_xboole_0) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_42) != iProver_top
% 0.83/1.00      | v1_funct_1(X0_42) != iProver_top ),
% 0.83/1.00      inference(renaming,[status(thm)],[c_1090]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_0,plain,
% 0.83/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f25]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_3,plain,
% 0.83/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_145,plain,
% 0.83/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 0.83/1.00      | X3 != X1
% 0.83/1.00      | k1_xboole_0 != X2 ),
% 0.83/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_146,plain,
% 0.83/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 0.83/1.00      inference(unflattening,[status(thm)],[c_145]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_440,plain,
% 0.83/1.00      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_43,k1_xboole_0)) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_146]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_685,plain,
% 0.83/1.00      ( r2_hidden(X0_42,k3_xboole_0(X0_43,k1_xboole_0)) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_2,plain,
% 0.83/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_453,plain,
% 0.83/1.00      ( k3_xboole_0(X0_43,k1_xboole_0) = k1_xboole_0 ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_704,plain,
% 0.83/1.00      ( r2_hidden(X0_42,k1_xboole_0) != iProver_top ),
% 0.83/1.00      inference(light_normalisation,[status(thm)],[c_685,c_453]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1098,plain,
% 0.83/1.00      ( v5_funct_1(k1_xboole_0,X0_42) = iProver_top
% 0.83/1.00      | v1_relat_1(X0_42) != iProver_top
% 0.83/1.00      | v1_funct_1(X0_42) != iProver_top ),
% 0.83/1.00      inference(forward_subsumption_resolution,
% 0.83/1.00                [status(thm)],
% 0.83/1.00                [c_1091,c_704]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_12,negated_conjecture,
% 0.83/1.00      ( ~ v5_funct_1(k1_xboole_0,sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_444,negated_conjecture,
% 0.83/1.00      ( ~ v5_funct_1(k1_xboole_0,sK2) ),
% 0.83/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_681,plain,
% 0.83/1.00      ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1102,plain,
% 0.83/1.00      ( v1_relat_1(sK2) != iProver_top | v1_funct_1(sK2) != iProver_top ),
% 0.83/1.00      inference(superposition,[status(thm)],[c_1098,c_681]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_13,negated_conjecture,
% 0.83/1.00      ( v1_funct_1(sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_16,plain,
% 0.83/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_14,negated_conjecture,
% 0.83/1.00      ( v1_relat_1(sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_15,plain,
% 0.83/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 0.83/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(contradiction,plain,
% 0.83/1.00      ( $false ),
% 0.83/1.00      inference(minisat,[status(thm)],[c_1102,c_16,c_15]) ).
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  ------                               Statistics
% 0.83/1.00  
% 0.83/1.00  ------ General
% 0.83/1.00  
% 0.83/1.00  abstr_ref_over_cycles:                  0
% 0.83/1.00  abstr_ref_under_cycles:                 0
% 0.83/1.00  gc_basic_clause_elim:                   0
% 0.83/1.00  forced_gc_time:                         0
% 0.83/1.00  parsing_time:                           0.007
% 0.83/1.00  unif_index_cands_time:                  0.
% 0.83/1.00  unif_index_add_time:                    0.
% 0.83/1.00  orderings_time:                         0.
% 0.83/1.00  out_proof_time:                         0.008
% 0.83/1.00  total_time:                             0.062
% 0.83/1.00  num_of_symbols:                         47
% 0.83/1.00  num_of_terms:                           1030
% 0.83/1.00  
% 0.83/1.00  ------ Preprocessing
% 0.83/1.00  
% 0.83/1.00  num_of_splits:                          0
% 0.83/1.00  num_of_split_atoms:                     0
% 0.83/1.00  num_of_reused_defs:                     0
% 0.83/1.00  num_eq_ax_congr_red:                    19
% 0.83/1.00  num_of_sem_filtered_clauses:            1
% 0.83/1.00  num_of_subtypes:                        2
% 0.83/1.00  monotx_restored_types:                  0
% 0.83/1.00  sat_num_of_epr_types:                   0
% 0.83/1.00  sat_num_of_non_cyclic_types:            0
% 0.83/1.00  sat_guarded_non_collapsed_types:        0
% 0.83/1.00  num_pure_diseq_elim:                    0
% 0.83/1.00  simp_replaced_by:                       0
% 0.83/1.00  res_preprocessed:                       80
% 0.83/1.00  prep_upred:                             0
% 0.83/1.00  prep_unflattend:                        12
% 0.83/1.00  smt_new_axioms:                         0
% 0.83/1.00  pred_elim_cands:                        4
% 0.83/1.00  pred_elim:                              1
% 0.83/1.00  pred_elim_cl:                           1
% 0.83/1.00  pred_elim_cycles:                       3
% 0.83/1.00  merged_defs:                            0
% 0.83/1.00  merged_defs_ncl:                        0
% 0.83/1.00  bin_hyper_res:                          0
% 0.83/1.00  prep_cycles:                            4
% 0.83/1.00  pred_elim_time:                         0.004
% 0.83/1.00  splitting_time:                         0.
% 0.83/1.00  sem_filter_time:                        0.
% 0.83/1.00  monotx_time:                            0.
% 0.83/1.00  subtype_inf_time:                       0.
% 0.83/1.00  
% 0.83/1.00  ------ Problem properties
% 0.83/1.00  
% 0.83/1.00  clauses:                                14
% 0.83/1.00  conjectures:                            3
% 0.83/1.00  epr:                                    3
% 0.83/1.00  horn:                                   13
% 0.83/1.00  ground:                                 6
% 0.83/1.00  unary:                                  10
% 0.83/1.00  binary:                                 1
% 0.83/1.00  lits:                                   31
% 0.83/1.00  lits_eq:                                4
% 0.83/1.00  fd_pure:                                0
% 0.83/1.00  fd_pseudo:                              0
% 0.83/1.00  fd_cond:                                0
% 0.83/1.00  fd_pseudo_cond:                         0
% 0.83/1.00  ac_symbols:                             0
% 0.83/1.00  
% 0.83/1.00  ------ Propositional Solver
% 0.83/1.00  
% 0.83/1.00  prop_solver_calls:                      26
% 0.83/1.00  prop_fast_solver_calls:                 475
% 0.83/1.00  smt_solver_calls:                       0
% 0.83/1.00  smt_fast_solver_calls:                  0
% 0.83/1.00  prop_num_of_clauses:                    289
% 0.83/1.00  prop_preprocess_simplified:             1930
% 0.83/1.00  prop_fo_subsumed:                       10
% 0.83/1.00  prop_solver_time:                       0.
% 0.83/1.00  smt_solver_time:                        0.
% 0.83/1.00  smt_fast_solver_time:                   0.
% 0.83/1.00  prop_fast_solver_time:                  0.
% 0.83/1.00  prop_unsat_core_time:                   0.
% 0.83/1.00  
% 0.83/1.00  ------ QBF
% 0.83/1.00  
% 0.83/1.00  qbf_q_res:                              0
% 0.83/1.00  qbf_num_tautologies:                    0
% 0.83/1.00  qbf_prep_cycles:                        0
% 0.83/1.00  
% 0.83/1.00  ------ BMC1
% 0.83/1.00  
% 0.83/1.00  bmc1_current_bound:                     -1
% 0.83/1.00  bmc1_last_solved_bound:                 -1
% 0.83/1.00  bmc1_unsat_core_size:                   -1
% 0.83/1.00  bmc1_unsat_core_parents_size:           -1
% 0.83/1.00  bmc1_merge_next_fun:                    0
% 0.83/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.00  
% 0.83/1.00  ------ Instantiation
% 0.83/1.00  
% 0.83/1.00  inst_num_of_clauses:                    78
% 0.83/1.00  inst_num_in_passive:                    14
% 0.83/1.00  inst_num_in_active:                     64
% 0.83/1.00  inst_num_in_unprocessed:                0
% 0.83/1.00  inst_num_of_loops:                      90
% 0.83/1.00  inst_num_of_learning_restarts:          0
% 0.83/1.00  inst_num_moves_active_passive:          21
% 0.83/1.00  inst_lit_activity:                      0
% 0.83/1.00  inst_lit_activity_moves:                0
% 0.83/1.00  inst_num_tautologies:                   0
% 0.83/1.00  inst_num_prop_implied:                  0
% 0.83/1.00  inst_num_existing_simplified:           0
% 0.83/1.00  inst_num_eq_res_simplified:             0
% 0.83/1.00  inst_num_child_elim:                    0
% 0.83/1.00  inst_num_of_dismatching_blockings:      4
% 0.83/1.00  inst_num_of_non_proper_insts:           58
% 0.83/1.00  inst_num_of_duplicates:                 0
% 0.83/1.00  inst_inst_num_from_inst_to_res:         0
% 0.83/1.00  inst_dismatching_checking_time:         0.
% 0.83/1.00  
% 0.83/1.00  ------ Resolution
% 0.83/1.00  
% 0.83/1.00  res_num_of_clauses:                     0
% 0.83/1.00  res_num_in_passive:                     0
% 0.83/1.00  res_num_in_active:                      0
% 0.83/1.00  res_num_of_loops:                       84
% 0.83/1.00  res_forward_subset_subsumed:            6
% 0.83/1.00  res_backward_subset_subsumed:           0
% 0.83/1.00  res_forward_subsumed:                   0
% 0.83/1.00  res_backward_subsumed:                  0
% 0.83/1.00  res_forward_subsumption_resolution:     0
% 0.83/1.00  res_backward_subsumption_resolution:    0
% 0.83/1.00  res_clause_to_clause_subsumption:       17
% 0.83/1.00  res_orphan_elimination:                 0
% 0.83/1.00  res_tautology_del:                      2
% 0.83/1.00  res_num_eq_res_simplified:              0
% 0.83/1.00  res_num_sel_changes:                    0
% 0.83/1.00  res_moves_from_active_to_pass:          0
% 0.83/1.00  
% 0.83/1.00  ------ Superposition
% 0.83/1.00  
% 0.83/1.00  sup_time_total:                         0.
% 0.83/1.00  sup_time_generating:                    0.
% 0.83/1.00  sup_time_sim_full:                      0.
% 0.83/1.00  sup_time_sim_immed:                     0.
% 0.83/1.00  
% 0.83/1.00  sup_num_of_clauses:                     19
% 0.83/1.00  sup_num_in_active:                      17
% 0.83/1.00  sup_num_in_passive:                     2
% 0.83/1.00  sup_num_of_loops:                       16
% 0.83/1.00  sup_fw_superposition:                   4
% 0.83/1.00  sup_bw_superposition:                   2
% 0.83/1.00  sup_immediate_simplified:               1
% 0.83/1.00  sup_given_eliminated:                   0
% 0.83/1.00  comparisons_done:                       0
% 0.83/1.00  comparisons_avoided:                    0
% 0.83/1.00  
% 0.83/1.00  ------ Simplifications
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  sim_fw_subset_subsumed:                 1
% 0.83/1.00  sim_bw_subset_subsumed:                 0
% 0.83/1.00  sim_fw_subsumed:                        0
% 0.83/1.00  sim_bw_subsumed:                        0
% 0.83/1.00  sim_fw_subsumption_res:                 1
% 0.83/1.00  sim_bw_subsumption_res:                 0
% 0.83/1.00  sim_tautology_del:                      1
% 0.83/1.00  sim_eq_tautology_del:                   0
% 0.83/1.00  sim_eq_res_simp:                        0
% 0.83/1.00  sim_fw_demodulated:                     0
% 0.83/1.00  sim_bw_demodulated:                     0
% 0.83/1.00  sim_light_normalised:                   1
% 0.83/1.00  sim_joinable_taut:                      0
% 0.83/1.00  sim_joinable_simp:                      0
% 0.83/1.00  sim_ac_normalised:                      0
% 0.83/1.00  sim_smt_subsumption:                    0
% 0.83/1.00  
%------------------------------------------------------------------------------
