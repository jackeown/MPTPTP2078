%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:42 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 642 expanded)
%              Number of clauses        :   87 ( 221 expanded)
%              Number of leaves         :   11 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  431 (2706 expanded)
%              Number of equality atoms :  189 ( 578 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK2))
      & v2_funct_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    & v2_funct_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).

fof(f37,plain,(
    ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_814,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k2_funct_1(X0_40))
    | ~ v1_funct_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1070,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k2_funct_1(X0_40)) = iProver_top
    | v1_funct_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_819,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v2_funct_1(X0_40)
    | k1_funct_1(X0_40,sK1(X0_40)) = k1_funct_1(X0_40,sK0(X0_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1065,plain,
    ( k1_funct_1(X0_40,sK1(X0_40)) = k1_funct_1(X0_40,sK0(X0_40))
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_1405,plain,
    ( k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_funct_1(k2_funct_1(X0_40)) != iProver_top
    | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1065])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_815,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v1_funct_1(k2_funct_1(X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_838,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_funct_1(k2_funct_1(X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_2204,plain,
    ( v1_funct_1(X0_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
    | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1405,c_838])).

cnf(c_2205,plain,
    ( k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2204])).

cnf(c_11,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_809,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1075,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_2214,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2205,c_1075])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_18,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_34,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_36,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1417,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_2311,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_15,c_16,c_18,c_36,c_1417])).

cnf(c_806,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1078,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_812,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | ~ v2_funct_1(X0_40)
    | k1_relat_1(k2_funct_1(X0_40)) = k2_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1072,plain,
    ( k1_relat_1(k2_funct_1(X0_40)) = k2_relat_1(X0_40)
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_1474,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1072])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_844,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1639,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1474,c_14,c_13,c_12,c_844])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_818,plain,
    ( r2_hidden(sK1(X0_40),k1_relat_1(X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v2_funct_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1066,plain,
    ( r2_hidden(sK1(X0_40),k1_relat_1(X0_40)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1643,plain,
    ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1066])).

cnf(c_31,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_584,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_585,plain,
    ( r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_586,plain,
    ( r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_822,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1255,plain,
    ( sK1(k2_funct_1(sK2)) = sK1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_825,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1265,plain,
    ( X0_42 != X1_42
    | X0_42 = k1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != X1_42 ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1309,plain,
    ( X0_42 != k2_relat_1(sK2)
    | X0_42 = k1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1371,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_823,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1372,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_827,plain,
    ( ~ r2_hidden(X0_41,X0_42)
    | r2_hidden(X1_41,X1_42)
    | X1_42 != X0_42
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_1237,plain,
    ( r2_hidden(X0_41,X0_42)
    | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | X0_42 != k1_relat_1(k2_funct_1(sK2))
    | X0_41 != sK1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1430,plain,
    ( r2_hidden(X0_41,k2_relat_1(sK2))
    | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | X0_41 != sK1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1461,plain,
    ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK1(k2_funct_1(sK2)) != sK1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_1462,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK1(k2_funct_1(sK2)) != sK1(k2_funct_1(sK2))
    | r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
    | r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_1757,plain,
    ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1643,c_14,c_15,c_13,c_16,c_12,c_33,c_36,c_586,c_844,c_1255,c_1371,c_1372,c_1462])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_810,plain,
    ( ~ r2_hidden(X0_41,k2_relat_1(X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | ~ v2_funct_1(X0_40)
    | k1_funct_1(X0_40,k1_funct_1(k2_funct_1(X0_40),X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1074,plain,
    ( k1_funct_1(X0_40,k1_funct_1(k2_funct_1(X0_40),X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(X0_40)) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_1855,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1074])).

cnf(c_32,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_35,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1526,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_1938,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_14,c_13,c_12,c_32,c_35,c_585,c_844,c_1255,c_1371,c_1372,c_1461,c_1526])).

cnf(c_2314,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_2311,c_1938])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_817,plain,
    ( r2_hidden(sK0(X0_40),k1_relat_1(X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v2_funct_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1067,plain,
    ( r2_hidden(sK0(X0_40),k1_relat_1(X0_40)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v2_funct_1(X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_1642,plain,
    ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1067])).

cnf(c_573,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_574,plain,
    ( r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_575,plain,
    ( r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_1453,plain,
    ( sK0(k2_funct_1(sK2)) = sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1232,plain,
    ( r2_hidden(X0_41,X0_42)
    | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | X0_42 != k1_relat_1(k2_funct_1(sK2))
    | X0_41 != sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1431,plain,
    ( r2_hidden(X0_41,k2_relat_1(sK2))
    | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | X0_41 != sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1502,plain,
    ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK0(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1504,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK0(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2))
    | r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
    | r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_1663,plain,
    ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1642,c_14,c_15,c_13,c_16,c_12,c_33,c_36,c_575,c_844,c_1371,c_1372,c_1453,c_1504])).

cnf(c_1856,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1074])).

cnf(c_1537,plain,
    ( ~ r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_2063,plain,
    ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1856,c_14,c_13,c_12,c_32,c_35,c_574,c_844,c_1371,c_1372,c_1453,c_1502,c_1537])).

cnf(c_2315,plain,
    ( sK1(k2_funct_1(sK2)) = sK0(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2314,c_2063])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_820,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v2_funct_1(X0_40)
    | sK1(X0_40) != sK0(X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1222,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | sK1(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2315,c_1222,c_35,c_32,c_11,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.88/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.88/1.01  
% 0.88/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.88/1.01  
% 0.88/1.01  ------  iProver source info
% 0.88/1.01  
% 0.88/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.88/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.88/1.01  git: non_committed_changes: false
% 0.88/1.01  git: last_make_outside_of_git: false
% 0.88/1.01  
% 0.88/1.01  ------ 
% 0.88/1.01  
% 0.88/1.01  ------ Input Options
% 0.88/1.01  
% 0.88/1.01  --out_options                           all
% 0.88/1.01  --tptp_safe_out                         true
% 0.88/1.01  --problem_path                          ""
% 0.88/1.01  --include_path                          ""
% 0.88/1.01  --clausifier                            res/vclausify_rel
% 0.88/1.01  --clausifier_options                    --mode clausify
% 0.88/1.01  --stdin                                 false
% 0.88/1.01  --stats_out                             all
% 0.88/1.01  
% 0.88/1.01  ------ General Options
% 0.88/1.01  
% 0.88/1.01  --fof                                   false
% 0.88/1.01  --time_out_real                         305.
% 0.88/1.01  --time_out_virtual                      -1.
% 0.88/1.01  --symbol_type_check                     false
% 0.88/1.01  --clausify_out                          false
% 0.88/1.01  --sig_cnt_out                           false
% 0.88/1.01  --trig_cnt_out                          false
% 0.88/1.01  --trig_cnt_out_tolerance                1.
% 0.88/1.01  --trig_cnt_out_sk_spl                   false
% 0.88/1.01  --abstr_cl_out                          false
% 0.88/1.01  
% 0.88/1.01  ------ Global Options
% 0.88/1.01  
% 0.88/1.01  --schedule                              default
% 0.88/1.01  --add_important_lit                     false
% 0.88/1.01  --prop_solver_per_cl                    1000
% 0.88/1.01  --min_unsat_core                        false
% 0.88/1.01  --soft_assumptions                      false
% 0.88/1.01  --soft_lemma_size                       3
% 0.88/1.01  --prop_impl_unit_size                   0
% 0.88/1.01  --prop_impl_unit                        []
% 0.88/1.01  --share_sel_clauses                     true
% 0.88/1.01  --reset_solvers                         false
% 0.88/1.01  --bc_imp_inh                            [conj_cone]
% 0.88/1.01  --conj_cone_tolerance                   3.
% 0.88/1.01  --extra_neg_conj                        none
% 0.88/1.01  --large_theory_mode                     true
% 0.88/1.01  --prolific_symb_bound                   200
% 0.88/1.01  --lt_threshold                          2000
% 0.88/1.01  --clause_weak_htbl                      true
% 0.88/1.01  --gc_record_bc_elim                     false
% 0.88/1.01  
% 0.88/1.01  ------ Preprocessing Options
% 0.88/1.01  
% 0.88/1.01  --preprocessing_flag                    true
% 0.88/1.01  --time_out_prep_mult                    0.1
% 0.88/1.01  --splitting_mode                        input
% 0.88/1.01  --splitting_grd                         true
% 0.88/1.01  --splitting_cvd                         false
% 0.88/1.01  --splitting_cvd_svl                     false
% 0.88/1.01  --splitting_nvd                         32
% 0.88/1.01  --sub_typing                            true
% 0.88/1.01  --prep_gs_sim                           true
% 0.88/1.01  --prep_unflatten                        true
% 0.88/1.01  --prep_res_sim                          true
% 0.88/1.01  --prep_upred                            true
% 0.88/1.01  --prep_sem_filter                       exhaustive
% 0.88/1.01  --prep_sem_filter_out                   false
% 0.88/1.01  --pred_elim                             true
% 0.88/1.01  --res_sim_input                         true
% 0.88/1.01  --eq_ax_congr_red                       true
% 0.88/1.01  --pure_diseq_elim                       true
% 0.88/1.01  --brand_transform                       false
% 0.88/1.01  --non_eq_to_eq                          false
% 0.88/1.01  --prep_def_merge                        true
% 0.88/1.01  --prep_def_merge_prop_impl              false
% 0.88/1.01  --prep_def_merge_mbd                    true
% 0.88/1.01  --prep_def_merge_tr_red                 false
% 0.88/1.01  --prep_def_merge_tr_cl                  false
% 0.88/1.01  --smt_preprocessing                     true
% 0.88/1.01  --smt_ac_axioms                         fast
% 0.88/1.01  --preprocessed_out                      false
% 0.88/1.01  --preprocessed_stats                    false
% 0.88/1.01  
% 0.88/1.01  ------ Abstraction refinement Options
% 0.88/1.01  
% 0.88/1.01  --abstr_ref                             []
% 0.88/1.01  --abstr_ref_prep                        false
% 0.88/1.01  --abstr_ref_until_sat                   false
% 0.88/1.01  --abstr_ref_sig_restrict                funpre
% 0.88/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/1.01  --abstr_ref_under                       []
% 0.88/1.01  
% 0.88/1.01  ------ SAT Options
% 0.88/1.01  
% 0.88/1.01  --sat_mode                              false
% 0.88/1.01  --sat_fm_restart_options                ""
% 0.88/1.01  --sat_gr_def                            false
% 0.88/1.01  --sat_epr_types                         true
% 0.88/1.01  --sat_non_cyclic_types                  false
% 0.88/1.01  --sat_finite_models                     false
% 0.88/1.01  --sat_fm_lemmas                         false
% 0.88/1.01  --sat_fm_prep                           false
% 0.88/1.01  --sat_fm_uc_incr                        true
% 0.88/1.01  --sat_out_model                         small
% 0.88/1.01  --sat_out_clauses                       false
% 0.88/1.01  
% 0.88/1.01  ------ QBF Options
% 0.88/1.01  
% 0.88/1.01  --qbf_mode                              false
% 0.88/1.01  --qbf_elim_univ                         false
% 0.88/1.01  --qbf_dom_inst                          none
% 0.88/1.01  --qbf_dom_pre_inst                      false
% 0.88/1.01  --qbf_sk_in                             false
% 0.88/1.01  --qbf_pred_elim                         true
% 0.88/1.01  --qbf_split                             512
% 0.88/1.01  
% 0.88/1.01  ------ BMC1 Options
% 0.88/1.01  
% 0.88/1.01  --bmc1_incremental                      false
% 0.88/1.01  --bmc1_axioms                           reachable_all
% 0.88/1.01  --bmc1_min_bound                        0
% 0.88/1.01  --bmc1_max_bound                        -1
% 0.88/1.01  --bmc1_max_bound_default                -1
% 0.88/1.01  --bmc1_symbol_reachability              true
% 0.88/1.01  --bmc1_property_lemmas                  false
% 0.88/1.01  --bmc1_k_induction                      false
% 0.88/1.01  --bmc1_non_equiv_states                 false
% 0.88/1.01  --bmc1_deadlock                         false
% 0.88/1.01  --bmc1_ucm                              false
% 0.88/1.01  --bmc1_add_unsat_core                   none
% 0.88/1.01  --bmc1_unsat_core_children              false
% 0.88/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/1.01  --bmc1_out_stat                         full
% 0.88/1.01  --bmc1_ground_init                      false
% 0.88/1.01  --bmc1_pre_inst_next_state              false
% 0.88/1.01  --bmc1_pre_inst_state                   false
% 0.88/1.01  --bmc1_pre_inst_reach_state             false
% 0.88/1.01  --bmc1_out_unsat_core                   false
% 0.88/1.01  --bmc1_aig_witness_out                  false
% 0.88/1.01  --bmc1_verbose                          false
% 0.88/1.01  --bmc1_dump_clauses_tptp                false
% 0.88/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.88/1.01  --bmc1_dump_file                        -
% 0.88/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.88/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.88/1.01  --bmc1_ucm_extend_mode                  1
% 0.88/1.01  --bmc1_ucm_init_mode                    2
% 0.88/1.01  --bmc1_ucm_cone_mode                    none
% 0.88/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.88/1.01  --bmc1_ucm_relax_model                  4
% 0.88/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.88/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/1.01  --bmc1_ucm_layered_model                none
% 0.88/1.01  --bmc1_ucm_max_lemma_size               10
% 0.88/1.01  
% 0.88/1.01  ------ AIG Options
% 0.88/1.01  
% 0.88/1.01  --aig_mode                              false
% 0.88/1.01  
% 0.88/1.01  ------ Instantiation Options
% 0.88/1.01  
% 0.88/1.01  --instantiation_flag                    true
% 0.88/1.01  --inst_sos_flag                         false
% 0.88/1.01  --inst_sos_phase                        true
% 0.88/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/1.01  --inst_lit_sel_side                     num_symb
% 0.88/1.01  --inst_solver_per_active                1400
% 0.88/1.01  --inst_solver_calls_frac                1.
% 0.88/1.01  --inst_passive_queue_type               priority_queues
% 0.88/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/1.01  --inst_passive_queues_freq              [25;2]
% 0.88/1.01  --inst_dismatching                      true
% 0.88/1.01  --inst_eager_unprocessed_to_passive     true
% 0.88/1.01  --inst_prop_sim_given                   true
% 0.88/1.01  --inst_prop_sim_new                     false
% 0.88/1.01  --inst_subs_new                         false
% 0.88/1.01  --inst_eq_res_simp                      false
% 0.88/1.01  --inst_subs_given                       false
% 0.88/1.01  --inst_orphan_elimination               true
% 0.88/1.01  --inst_learning_loop_flag               true
% 0.88/1.01  --inst_learning_start                   3000
% 0.88/1.01  --inst_learning_factor                  2
% 0.88/1.01  --inst_start_prop_sim_after_learn       3
% 0.88/1.01  --inst_sel_renew                        solver
% 0.88/1.01  --inst_lit_activity_flag                true
% 0.88/1.01  --inst_restr_to_given                   false
% 0.88/1.01  --inst_activity_threshold               500
% 0.88/1.01  --inst_out_proof                        true
% 0.88/1.01  
% 0.88/1.01  ------ Resolution Options
% 0.88/1.01  
% 0.88/1.01  --resolution_flag                       true
% 0.88/1.01  --res_lit_sel                           adaptive
% 0.88/1.01  --res_lit_sel_side                      none
% 0.88/1.01  --res_ordering                          kbo
% 0.88/1.01  --res_to_prop_solver                    active
% 0.88/1.01  --res_prop_simpl_new                    false
% 0.88/1.01  --res_prop_simpl_given                  true
% 0.88/1.01  --res_passive_queue_type                priority_queues
% 0.88/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/1.01  --res_passive_queues_freq               [15;5]
% 0.88/1.01  --res_forward_subs                      full
% 0.88/1.01  --res_backward_subs                     full
% 0.88/1.01  --res_forward_subs_resolution           true
% 0.88/1.01  --res_backward_subs_resolution          true
% 0.88/1.01  --res_orphan_elimination                true
% 0.88/1.01  --res_time_limit                        2.
% 0.88/1.01  --res_out_proof                         true
% 0.88/1.01  
% 0.88/1.01  ------ Superposition Options
% 0.88/1.01  
% 0.88/1.01  --superposition_flag                    true
% 0.88/1.01  --sup_passive_queue_type                priority_queues
% 0.88/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.88/1.01  --demod_completeness_check              fast
% 0.88/1.01  --demod_use_ground                      true
% 0.88/1.01  --sup_to_prop_solver                    passive
% 0.88/1.01  --sup_prop_simpl_new                    true
% 0.88/1.01  --sup_prop_simpl_given                  true
% 0.88/1.01  --sup_fun_splitting                     false
% 0.88/1.01  --sup_smt_interval                      50000
% 0.88/1.01  
% 0.88/1.01  ------ Superposition Simplification Setup
% 0.88/1.01  
% 0.88/1.01  --sup_indices_passive                   []
% 0.88/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_full_bw                           [BwDemod]
% 0.88/1.01  --sup_immed_triv                        [TrivRules]
% 0.88/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_immed_bw_main                     []
% 0.88/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.01  
% 0.88/1.01  ------ Combination Options
% 0.88/1.01  
% 0.88/1.01  --comb_res_mult                         3
% 0.88/1.01  --comb_sup_mult                         2
% 0.88/1.01  --comb_inst_mult                        10
% 0.88/1.01  
% 0.88/1.01  ------ Debug Options
% 0.88/1.01  
% 0.88/1.01  --dbg_backtrace                         false
% 0.88/1.01  --dbg_dump_prop_clauses                 false
% 0.88/1.01  --dbg_dump_prop_clauses_file            -
% 0.88/1.01  --dbg_out_stat                          false
% 0.88/1.01  ------ Parsing...
% 0.88/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.88/1.01  
% 0.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.88/1.01  
% 0.88/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.88/1.01  
% 0.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.88/1.01  ------ Proving...
% 0.88/1.01  ------ Problem Properties 
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  clauses                                 15
% 0.88/1.01  conjectures                             4
% 0.88/1.01  EPR                                     3
% 0.88/1.01  Horn                                    12
% 0.88/1.01  unary                                   4
% 0.88/1.01  binary                                  0
% 0.88/1.01  lits                                    51
% 0.88/1.01  lits eq                                 8
% 0.88/1.01  fd_pure                                 0
% 0.88/1.01  fd_pseudo                               0
% 0.88/1.01  fd_cond                                 0
% 0.88/1.01  fd_pseudo_cond                          1
% 0.88/1.01  AC symbols                              0
% 0.88/1.01  
% 0.88/1.01  ------ Schedule dynamic 5 is on 
% 0.88/1.01  
% 0.88/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  ------ 
% 0.88/1.01  Current options:
% 0.88/1.01  ------ 
% 0.88/1.01  
% 0.88/1.01  ------ Input Options
% 0.88/1.01  
% 0.88/1.01  --out_options                           all
% 0.88/1.01  --tptp_safe_out                         true
% 0.88/1.01  --problem_path                          ""
% 0.88/1.01  --include_path                          ""
% 0.88/1.01  --clausifier                            res/vclausify_rel
% 0.88/1.01  --clausifier_options                    --mode clausify
% 0.88/1.01  --stdin                                 false
% 0.88/1.01  --stats_out                             all
% 0.88/1.01  
% 0.88/1.01  ------ General Options
% 0.88/1.01  
% 0.88/1.01  --fof                                   false
% 0.88/1.01  --time_out_real                         305.
% 0.88/1.01  --time_out_virtual                      -1.
% 0.88/1.01  --symbol_type_check                     false
% 0.88/1.01  --clausify_out                          false
% 0.88/1.01  --sig_cnt_out                           false
% 0.88/1.01  --trig_cnt_out                          false
% 0.88/1.01  --trig_cnt_out_tolerance                1.
% 0.88/1.01  --trig_cnt_out_sk_spl                   false
% 0.88/1.01  --abstr_cl_out                          false
% 0.88/1.01  
% 0.88/1.01  ------ Global Options
% 0.88/1.01  
% 0.88/1.01  --schedule                              default
% 0.88/1.01  --add_important_lit                     false
% 0.88/1.01  --prop_solver_per_cl                    1000
% 0.88/1.01  --min_unsat_core                        false
% 0.88/1.01  --soft_assumptions                      false
% 0.88/1.01  --soft_lemma_size                       3
% 0.88/1.01  --prop_impl_unit_size                   0
% 0.88/1.01  --prop_impl_unit                        []
% 0.88/1.01  --share_sel_clauses                     true
% 0.88/1.01  --reset_solvers                         false
% 0.88/1.01  --bc_imp_inh                            [conj_cone]
% 0.88/1.01  --conj_cone_tolerance                   3.
% 0.88/1.01  --extra_neg_conj                        none
% 0.88/1.01  --large_theory_mode                     true
% 0.88/1.01  --prolific_symb_bound                   200
% 0.88/1.01  --lt_threshold                          2000
% 0.88/1.01  --clause_weak_htbl                      true
% 0.88/1.01  --gc_record_bc_elim                     false
% 0.88/1.01  
% 0.88/1.01  ------ Preprocessing Options
% 0.88/1.01  
% 0.88/1.01  --preprocessing_flag                    true
% 0.88/1.01  --time_out_prep_mult                    0.1
% 0.88/1.01  --splitting_mode                        input
% 0.88/1.01  --splitting_grd                         true
% 0.88/1.01  --splitting_cvd                         false
% 0.88/1.01  --splitting_cvd_svl                     false
% 0.88/1.01  --splitting_nvd                         32
% 0.88/1.01  --sub_typing                            true
% 0.88/1.01  --prep_gs_sim                           true
% 0.88/1.01  --prep_unflatten                        true
% 0.88/1.01  --prep_res_sim                          true
% 0.88/1.01  --prep_upred                            true
% 0.88/1.01  --prep_sem_filter                       exhaustive
% 0.88/1.01  --prep_sem_filter_out                   false
% 0.88/1.01  --pred_elim                             true
% 0.88/1.01  --res_sim_input                         true
% 0.88/1.01  --eq_ax_congr_red                       true
% 0.88/1.01  --pure_diseq_elim                       true
% 0.88/1.01  --brand_transform                       false
% 0.88/1.01  --non_eq_to_eq                          false
% 0.88/1.01  --prep_def_merge                        true
% 0.88/1.01  --prep_def_merge_prop_impl              false
% 0.88/1.01  --prep_def_merge_mbd                    true
% 0.88/1.01  --prep_def_merge_tr_red                 false
% 0.88/1.01  --prep_def_merge_tr_cl                  false
% 0.88/1.01  --smt_preprocessing                     true
% 0.88/1.01  --smt_ac_axioms                         fast
% 0.88/1.01  --preprocessed_out                      false
% 0.88/1.01  --preprocessed_stats                    false
% 0.88/1.01  
% 0.88/1.01  ------ Abstraction refinement Options
% 0.88/1.01  
% 0.88/1.01  --abstr_ref                             []
% 0.88/1.01  --abstr_ref_prep                        false
% 0.88/1.01  --abstr_ref_until_sat                   false
% 0.88/1.01  --abstr_ref_sig_restrict                funpre
% 0.88/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/1.01  --abstr_ref_under                       []
% 0.88/1.01  
% 0.88/1.01  ------ SAT Options
% 0.88/1.01  
% 0.88/1.01  --sat_mode                              false
% 0.88/1.01  --sat_fm_restart_options                ""
% 0.88/1.01  --sat_gr_def                            false
% 0.88/1.01  --sat_epr_types                         true
% 0.88/1.01  --sat_non_cyclic_types                  false
% 0.88/1.01  --sat_finite_models                     false
% 0.88/1.01  --sat_fm_lemmas                         false
% 0.88/1.01  --sat_fm_prep                           false
% 0.88/1.01  --sat_fm_uc_incr                        true
% 0.88/1.01  --sat_out_model                         small
% 0.88/1.01  --sat_out_clauses                       false
% 0.88/1.01  
% 0.88/1.01  ------ QBF Options
% 0.88/1.01  
% 0.88/1.01  --qbf_mode                              false
% 0.88/1.01  --qbf_elim_univ                         false
% 0.88/1.01  --qbf_dom_inst                          none
% 0.88/1.01  --qbf_dom_pre_inst                      false
% 0.88/1.01  --qbf_sk_in                             false
% 0.88/1.01  --qbf_pred_elim                         true
% 0.88/1.01  --qbf_split                             512
% 0.88/1.01  
% 0.88/1.01  ------ BMC1 Options
% 0.88/1.01  
% 0.88/1.01  --bmc1_incremental                      false
% 0.88/1.01  --bmc1_axioms                           reachable_all
% 0.88/1.01  --bmc1_min_bound                        0
% 0.88/1.01  --bmc1_max_bound                        -1
% 0.88/1.01  --bmc1_max_bound_default                -1
% 0.88/1.01  --bmc1_symbol_reachability              true
% 0.88/1.01  --bmc1_property_lemmas                  false
% 0.88/1.01  --bmc1_k_induction                      false
% 0.88/1.01  --bmc1_non_equiv_states                 false
% 0.88/1.01  --bmc1_deadlock                         false
% 0.88/1.01  --bmc1_ucm                              false
% 0.88/1.01  --bmc1_add_unsat_core                   none
% 0.88/1.01  --bmc1_unsat_core_children              false
% 0.88/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/1.01  --bmc1_out_stat                         full
% 0.88/1.01  --bmc1_ground_init                      false
% 0.88/1.01  --bmc1_pre_inst_next_state              false
% 0.88/1.01  --bmc1_pre_inst_state                   false
% 0.88/1.01  --bmc1_pre_inst_reach_state             false
% 0.88/1.01  --bmc1_out_unsat_core                   false
% 0.88/1.01  --bmc1_aig_witness_out                  false
% 0.88/1.01  --bmc1_verbose                          false
% 0.88/1.01  --bmc1_dump_clauses_tptp                false
% 0.88/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.88/1.01  --bmc1_dump_file                        -
% 0.88/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.88/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.88/1.01  --bmc1_ucm_extend_mode                  1
% 0.88/1.01  --bmc1_ucm_init_mode                    2
% 0.88/1.01  --bmc1_ucm_cone_mode                    none
% 0.88/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.88/1.01  --bmc1_ucm_relax_model                  4
% 0.88/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.88/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/1.01  --bmc1_ucm_layered_model                none
% 0.88/1.01  --bmc1_ucm_max_lemma_size               10
% 0.88/1.01  
% 0.88/1.01  ------ AIG Options
% 0.88/1.01  
% 0.88/1.01  --aig_mode                              false
% 0.88/1.01  
% 0.88/1.01  ------ Instantiation Options
% 0.88/1.01  
% 0.88/1.01  --instantiation_flag                    true
% 0.88/1.01  --inst_sos_flag                         false
% 0.88/1.01  --inst_sos_phase                        true
% 0.88/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/1.01  --inst_lit_sel_side                     none
% 0.88/1.01  --inst_solver_per_active                1400
% 0.88/1.01  --inst_solver_calls_frac                1.
% 0.88/1.01  --inst_passive_queue_type               priority_queues
% 0.88/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/1.01  --inst_passive_queues_freq              [25;2]
% 0.88/1.01  --inst_dismatching                      true
% 0.88/1.01  --inst_eager_unprocessed_to_passive     true
% 0.88/1.01  --inst_prop_sim_given                   true
% 0.88/1.01  --inst_prop_sim_new                     false
% 0.88/1.01  --inst_subs_new                         false
% 0.88/1.01  --inst_eq_res_simp                      false
% 0.88/1.01  --inst_subs_given                       false
% 0.88/1.01  --inst_orphan_elimination               true
% 0.88/1.01  --inst_learning_loop_flag               true
% 0.88/1.01  --inst_learning_start                   3000
% 0.88/1.01  --inst_learning_factor                  2
% 0.88/1.01  --inst_start_prop_sim_after_learn       3
% 0.88/1.01  --inst_sel_renew                        solver
% 0.88/1.01  --inst_lit_activity_flag                true
% 0.88/1.01  --inst_restr_to_given                   false
% 0.88/1.01  --inst_activity_threshold               500
% 0.88/1.01  --inst_out_proof                        true
% 0.88/1.01  
% 0.88/1.01  ------ Resolution Options
% 0.88/1.01  
% 0.88/1.01  --resolution_flag                       false
% 0.88/1.01  --res_lit_sel                           adaptive
% 0.88/1.01  --res_lit_sel_side                      none
% 0.88/1.01  --res_ordering                          kbo
% 0.88/1.01  --res_to_prop_solver                    active
% 0.88/1.01  --res_prop_simpl_new                    false
% 0.88/1.01  --res_prop_simpl_given                  true
% 0.88/1.01  --res_passive_queue_type                priority_queues
% 0.88/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/1.01  --res_passive_queues_freq               [15;5]
% 0.88/1.01  --res_forward_subs                      full
% 0.88/1.01  --res_backward_subs                     full
% 0.88/1.01  --res_forward_subs_resolution           true
% 0.88/1.01  --res_backward_subs_resolution          true
% 0.88/1.01  --res_orphan_elimination                true
% 0.88/1.01  --res_time_limit                        2.
% 0.88/1.01  --res_out_proof                         true
% 0.88/1.01  
% 0.88/1.01  ------ Superposition Options
% 0.88/1.01  
% 0.88/1.01  --superposition_flag                    true
% 0.88/1.01  --sup_passive_queue_type                priority_queues
% 0.88/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.88/1.01  --demod_completeness_check              fast
% 0.88/1.01  --demod_use_ground                      true
% 0.88/1.01  --sup_to_prop_solver                    passive
% 0.88/1.01  --sup_prop_simpl_new                    true
% 0.88/1.01  --sup_prop_simpl_given                  true
% 0.88/1.01  --sup_fun_splitting                     false
% 0.88/1.01  --sup_smt_interval                      50000
% 0.88/1.01  
% 0.88/1.01  ------ Superposition Simplification Setup
% 0.88/1.01  
% 0.88/1.01  --sup_indices_passive                   []
% 0.88/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_full_bw                           [BwDemod]
% 0.88/1.01  --sup_immed_triv                        [TrivRules]
% 0.88/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_immed_bw_main                     []
% 0.88/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.01  
% 0.88/1.01  ------ Combination Options
% 0.88/1.01  
% 0.88/1.01  --comb_res_mult                         3
% 0.88/1.01  --comb_sup_mult                         2
% 0.88/1.01  --comb_inst_mult                        10
% 0.88/1.01  
% 0.88/1.01  ------ Debug Options
% 0.88/1.01  
% 0.88/1.01  --dbg_backtrace                         false
% 0.88/1.01  --dbg_dump_prop_clauses                 false
% 0.88/1.01  --dbg_dump_prop_clauses_file            -
% 0.88/1.01  --dbg_out_stat                          false
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  ------ Proving...
% 0.88/1.01  
% 0.88/1.01  
% 0.88/1.01  % SZS status Theorem for theBenchmark.p
% 0.88/1.01  
% 0.88/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.88/1.01  
% 0.88/1.01  fof(f2,axiom,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.01  
% 0.88/1.01  fof(f9,plain,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.88/1.01    inference(ennf_transformation,[],[f2])).
% 0.88/1.01  
% 0.88/1.01  fof(f10,plain,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(flattening,[],[f9])).
% 0.88/1.01  
% 0.88/1.01  fof(f28,plain,(
% 0.88/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f10])).
% 0.88/1.01  
% 0.88/1.01  fof(f1,axiom,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.01  
% 0.88/1.01  fof(f7,plain,(
% 0.88/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.88/1.01    inference(ennf_transformation,[],[f1])).
% 0.88/1.01  
% 0.88/1.01  fof(f8,plain,(
% 0.88/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(flattening,[],[f7])).
% 0.88/1.01  
% 0.88/1.01  fof(f17,plain,(
% 0.88/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(nnf_transformation,[],[f8])).
% 0.88/1.01  
% 0.88/1.01  fof(f18,plain,(
% 0.88/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(rectify,[],[f17])).
% 0.88/1.01  
% 0.88/1.01  fof(f19,plain,(
% 0.88/1.01    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 0.88/1.01    introduced(choice_axiom,[])).
% 0.88/1.01  
% 0.88/1.01  fof(f20,plain,(
% 0.88/1.01    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.88/1.01  
% 0.88/1.01  fof(f26,plain,(
% 0.88/1.01    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f20])).
% 0.88/1.01  
% 0.88/1.01  fof(f29,plain,(
% 0.88/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f10])).
% 0.88/1.01  
% 0.88/1.01  fof(f5,conjecture,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.01  
% 0.88/1.01  fof(f6,negated_conjecture,(
% 0.88/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.88/1.01    inference(negated_conjecture,[],[f5])).
% 0.88/1.01  
% 0.88/1.01  fof(f15,plain,(
% 0.88/1.01    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.88/1.01    inference(ennf_transformation,[],[f6])).
% 0.88/1.01  
% 0.88/1.01  fof(f16,plain,(
% 0.88/1.01    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.88/1.01    inference(flattening,[],[f15])).
% 0.88/1.01  
% 0.88/1.01  fof(f21,plain,(
% 0.88/1.01    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK2)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.88/1.01    introduced(choice_axiom,[])).
% 0.88/1.01  
% 0.88/1.01  fof(f22,plain,(
% 0.88/1.01    ~v2_funct_1(k2_funct_1(sK2)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.88/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).
% 0.88/1.01  
% 0.88/1.01  fof(f37,plain,(
% 0.88/1.01    ~v2_funct_1(k2_funct_1(sK2))),
% 0.88/1.01    inference(cnf_transformation,[],[f22])).
% 0.88/1.01  
% 0.88/1.01  fof(f34,plain,(
% 0.88/1.01    v1_relat_1(sK2)),
% 0.88/1.01    inference(cnf_transformation,[],[f22])).
% 0.88/1.01  
% 0.88/1.01  fof(f35,plain,(
% 0.88/1.01    v1_funct_1(sK2)),
% 0.88/1.01    inference(cnf_transformation,[],[f22])).
% 0.88/1.01  
% 0.88/1.01  fof(f3,axiom,(
% 0.88/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 0.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.01  
% 0.88/1.01  fof(f11,plain,(
% 0.88/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.88/1.01    inference(ennf_transformation,[],[f3])).
% 0.88/1.01  
% 0.88/1.01  fof(f12,plain,(
% 0.88/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.88/1.01    inference(flattening,[],[f11])).
% 0.88/1.01  
% 0.88/1.01  fof(f30,plain,(
% 0.88/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f12])).
% 0.88/1.01  
% 0.88/1.01  fof(f36,plain,(
% 0.88/1.01    v2_funct_1(sK2)),
% 0.88/1.01    inference(cnf_transformation,[],[f22])).
% 0.88/1.01  
% 0.88/1.01  fof(f25,plain,(
% 0.88/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f20])).
% 0.88/1.01  
% 0.88/1.01  fof(f4,axiom,(
% 0.88/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.88/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.01  
% 0.88/1.01  fof(f13,plain,(
% 0.88/1.01    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.88/1.01    inference(ennf_transformation,[],[f4])).
% 0.88/1.01  
% 0.88/1.01  fof(f14,plain,(
% 0.88/1.01    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.88/1.01    inference(flattening,[],[f13])).
% 0.88/1.01  
% 0.88/1.01  fof(f32,plain,(
% 0.88/1.01    ( ! [X0,X1] : (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f14])).
% 0.88/1.01  
% 0.88/1.01  fof(f24,plain,(
% 0.88/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f20])).
% 0.88/1.01  
% 0.88/1.01  fof(f27,plain,(
% 0.88/1.01    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.88/1.01    inference(cnf_transformation,[],[f20])).
% 0.88/1.01  
% 0.88/1.01  cnf(c_6,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0)
% 0.88/1.01      | v1_relat_1(k2_funct_1(X0))
% 0.88/1.01      | ~ v1_funct_1(X0) ),
% 0.88/1.01      inference(cnf_transformation,[],[f28]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_814,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0_40)
% 0.88/1.01      | v1_relat_1(k2_funct_1(X0_40))
% 0.88/1.01      | ~ v1_funct_1(X0_40) ),
% 0.88/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_1070,plain,
% 0.88/1.01      ( v1_relat_1(X0_40) != iProver_top
% 0.88/1.01      | v1_relat_1(k2_funct_1(X0_40)) = iProver_top
% 0.88/1.01      | v1_funct_1(X0_40) != iProver_top ),
% 0.88/1.01      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_1,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0)
% 0.88/1.01      | ~ v1_funct_1(X0)
% 0.88/1.01      | v2_funct_1(X0)
% 0.88/1.01      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 0.88/1.01      inference(cnf_transformation,[],[f26]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_819,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0_40)
% 0.88/1.01      | ~ v1_funct_1(X0_40)
% 0.88/1.01      | v2_funct_1(X0_40)
% 0.88/1.01      | k1_funct_1(X0_40,sK1(X0_40)) = k1_funct_1(X0_40,sK0(X0_40)) ),
% 0.88/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_1065,plain,
% 0.88/1.01      ( k1_funct_1(X0_40,sK1(X0_40)) = k1_funct_1(X0_40,sK0(X0_40))
% 0.88/1.01      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.01      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.01      | v2_funct_1(X0_40) = iProver_top ),
% 0.88/1.01      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_1405,plain,
% 0.88/1.01      ( k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
% 0.88/1.01      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.01      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.01      | v1_funct_1(k2_funct_1(X0_40)) != iProver_top
% 0.88/1.01      | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
% 0.88/1.01      inference(superposition,[status(thm)],[c_1070,c_1065]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_5,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0)
% 0.88/1.01      | ~ v1_funct_1(X0)
% 0.88/1.01      | v1_funct_1(k2_funct_1(X0)) ),
% 0.88/1.01      inference(cnf_transformation,[],[f29]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_815,plain,
% 0.88/1.01      ( ~ v1_relat_1(X0_40)
% 0.88/1.01      | ~ v1_funct_1(X0_40)
% 0.88/1.01      | v1_funct_1(k2_funct_1(X0_40)) ),
% 0.88/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_838,plain,
% 0.88/1.01      ( v1_relat_1(X0_40) != iProver_top
% 0.88/1.01      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.01      | v1_funct_1(k2_funct_1(X0_40)) = iProver_top ),
% 0.88/1.01      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 0.88/1.01  
% 0.88/1.01  cnf(c_2204,plain,
% 0.88/1.01      ( v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
% 0.88/1.02      | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1405,c_838]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2205,plain,
% 0.88/1.02      ( k1_funct_1(k2_funct_1(X0_40),sK0(k2_funct_1(X0_40))) = k1_funct_1(k2_funct_1(X0_40),sK1(k2_funct_1(X0_40)))
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v2_funct_1(k2_funct_1(X0_40)) = iProver_top ),
% 0.88/1.02      inference(renaming,[status(thm)],[c_2204]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_11,negated_conjecture,
% 0.88/1.02      ( ~ v2_funct_1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(cnf_transformation,[],[f37]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_809,negated_conjecture,
% 0.88/1.02      ( ~ v2_funct_1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1075,plain,
% 0.88/1.02      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2214,plain,
% 0.88/1.02      ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))
% 0.88/1.02      | v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_2205,c_1075]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_14,negated_conjecture,
% 0.88/1.02      ( v1_relat_1(sK2) ),
% 0.88/1.02      inference(cnf_transformation,[],[f34]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_15,plain,
% 0.88/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_13,negated_conjecture,
% 0.88/1.02      ( v1_funct_1(sK2) ),
% 0.88/1.02      inference(cnf_transformation,[],[f35]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_16,plain,
% 0.88/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_18,plain,
% 0.88/1.02      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_34,plain,
% 0.88/1.02      ( v1_relat_1(X0) != iProver_top
% 0.88/1.02      | v1_funct_1(X0) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_36,plain,
% 0.88/1.02      ( v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_34]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1417,plain,
% 0.88/1.02      ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))
% 0.88/1.02      | v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top
% 0.88/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1405]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2311,plain,
% 0.88/1.02      ( k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2))) ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_2214,c_15,c_16,c_18,c_36,c_1417]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_806,negated_conjecture,
% 0.88/1.02      ( v1_relat_1(sK2) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1078,plain,
% 0.88/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_8,plain,
% 0.88/1.02      ( ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | ~ v2_funct_1(X0)
% 0.88/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.88/1.02      inference(cnf_transformation,[],[f30]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_812,plain,
% 0.88/1.02      ( ~ v1_relat_1(X0_40)
% 0.88/1.02      | ~ v1_funct_1(X0_40)
% 0.88/1.02      | ~ v2_funct_1(X0_40)
% 0.88/1.02      | k1_relat_1(k2_funct_1(X0_40)) = k2_relat_1(X0_40) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1072,plain,
% 0.88/1.02      ( k1_relat_1(k2_funct_1(X0_40)) = k2_relat_1(X0_40)
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v2_funct_1(X0_40) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1474,plain,
% 0.88/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top
% 0.88/1.02      | v2_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_1078,c_1072]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_12,negated_conjecture,
% 0.88/1.02      ( v2_funct_1(sK2) ),
% 0.88/1.02      inference(cnf_transformation,[],[f36]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_844,plain,
% 0.88/1.02      ( ~ v1_relat_1(sK2)
% 0.88/1.02      | ~ v1_funct_1(sK2)
% 0.88/1.02      | ~ v2_funct_1(sK2)
% 0.88/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_812]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1639,plain,
% 0.88/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1474,c_14,c_13,c_12,c_844]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2,plain,
% 0.88/1.02      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 0.88/1.02      | ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | v2_funct_1(X0) ),
% 0.88/1.02      inference(cnf_transformation,[],[f25]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_818,plain,
% 0.88/1.02      ( r2_hidden(sK1(X0_40),k1_relat_1(X0_40))
% 0.88/1.02      | ~ v1_relat_1(X0_40)
% 0.88/1.02      | ~ v1_funct_1(X0_40)
% 0.88/1.02      | v2_funct_1(X0_40) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1066,plain,
% 0.88/1.02      ( r2_hidden(sK1(X0_40),k1_relat_1(X0_40)) = iProver_top
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v2_funct_1(X0_40) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1643,plain,
% 0.88/1.02      ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
% 0.88/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_1639,c_1066]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_31,plain,
% 0.88/1.02      ( v1_relat_1(X0) != iProver_top
% 0.88/1.02      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 0.88/1.02      | v1_funct_1(X0) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_33,plain,
% 0.88/1.02      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 0.88/1.02      | v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_31]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_584,plain,
% 0.88/1.02      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 0.88/1.02      | ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | k2_funct_1(sK2) != X0 ),
% 0.88/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_585,plain,
% 0.88/1.02      ( r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | ~ v1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(unflattening,[status(thm)],[c_584]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_586,plain,
% 0.88/1.02      ( r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) = iProver_top
% 0.88/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_822,plain,( X0_41 = X0_41 ),theory(equality) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1255,plain,
% 0.88/1.02      ( sK1(k2_funct_1(sK2)) = sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_822]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_825,plain,
% 0.88/1.02      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.88/1.02      theory(equality) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1265,plain,
% 0.88/1.02      ( X0_42 != X1_42
% 0.88/1.02      | X0_42 = k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | k1_relat_1(k2_funct_1(sK2)) != X1_42 ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_825]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1309,plain,
% 0.88/1.02      ( X0_42 != k2_relat_1(sK2)
% 0.88/1.02      | X0_42 = k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1265]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1371,plain,
% 0.88/1.02      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 0.88/1.02      | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1309]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_823,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1372,plain,
% 0.88/1.02      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_823]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_827,plain,
% 0.88/1.02      ( ~ r2_hidden(X0_41,X0_42)
% 0.88/1.02      | r2_hidden(X1_41,X1_42)
% 0.88/1.02      | X1_42 != X0_42
% 0.88/1.02      | X1_41 != X0_41 ),
% 0.88/1.02      theory(equality) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1237,plain,
% 0.88/1.02      ( r2_hidden(X0_41,X0_42)
% 0.88/1.02      | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | X0_42 != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | X0_41 != sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_827]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1430,plain,
% 0.88/1.02      ( r2_hidden(X0_41,k2_relat_1(sK2))
% 0.88/1.02      | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | X0_41 != sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1237]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1461,plain,
% 0.88/1.02      ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2))
% 0.88/1.02      | ~ r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | sK1(k2_funct_1(sK2)) != sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1430]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1462,plain,
% 0.88/1.02      ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | sK1(k2_funct_1(sK2)) != sK1(k2_funct_1(sK2))
% 0.88/1.02      | r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
% 0.88/1.02      | r2_hidden(sK1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1757,plain,
% 0.88/1.02      ( r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1643,c_14,c_15,c_13,c_16,c_12,c_33,c_36,c_586,c_844,
% 0.88/1.02                 c_1255,c_1371,c_1372,c_1462]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_10,plain,
% 0.88/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 0.88/1.02      | ~ v1_relat_1(X1)
% 0.88/1.02      | ~ v1_funct_1(X1)
% 0.88/1.02      | ~ v2_funct_1(X1)
% 0.88/1.02      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
% 0.88/1.02      inference(cnf_transformation,[],[f32]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_810,plain,
% 0.88/1.02      ( ~ r2_hidden(X0_41,k2_relat_1(X0_40))
% 0.88/1.02      | ~ v1_relat_1(X0_40)
% 0.88/1.02      | ~ v1_funct_1(X0_40)
% 0.88/1.02      | ~ v2_funct_1(X0_40)
% 0.88/1.02      | k1_funct_1(X0_40,k1_funct_1(k2_funct_1(X0_40),X0_41)) = X0_41 ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1074,plain,
% 0.88/1.02      ( k1_funct_1(X0_40,k1_funct_1(k2_funct_1(X0_40),X0_41)) = X0_41
% 0.88/1.02      | r2_hidden(X0_41,k2_relat_1(X0_40)) != iProver_top
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v2_funct_1(X0_40) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1855,plain,
% 0.88/1.02      ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2))
% 0.88/1.02      | v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top
% 0.88/1.02      | v2_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_1757,c_1074]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_32,plain,
% 0.88/1.02      ( v1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | ~ v1_relat_1(sK2)
% 0.88/1.02      | ~ v1_funct_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_35,plain,
% 0.88/1.02      ( ~ v1_relat_1(sK2)
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2))
% 0.88/1.02      | ~ v1_funct_1(sK2) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1526,plain,
% 0.88/1.02      ( ~ r2_hidden(sK1(k2_funct_1(sK2)),k2_relat_1(sK2))
% 0.88/1.02      | ~ v1_relat_1(sK2)
% 0.88/1.02      | ~ v1_funct_1(sK2)
% 0.88/1.02      | ~ v2_funct_1(sK2)
% 0.88/1.02      | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_810]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1938,plain,
% 0.88/1.02      ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK1(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1855,c_14,c_13,c_12,c_32,c_35,c_585,c_844,c_1255,
% 0.88/1.02                 c_1371,c_1372,c_1461,c_1526]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2314,plain,
% 0.88/1.02      ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(demodulation,[status(thm)],[c_2311,c_1938]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_3,plain,
% 0.88/1.02      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 0.88/1.02      | ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | v2_funct_1(X0) ),
% 0.88/1.02      inference(cnf_transformation,[],[f24]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_817,plain,
% 0.88/1.02      ( r2_hidden(sK0(X0_40),k1_relat_1(X0_40))
% 0.88/1.02      | ~ v1_relat_1(X0_40)
% 0.88/1.02      | ~ v1_funct_1(X0_40)
% 0.88/1.02      | v2_funct_1(X0_40) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1067,plain,
% 0.88/1.02      ( r2_hidden(sK0(X0_40),k1_relat_1(X0_40)) = iProver_top
% 0.88/1.02      | v1_relat_1(X0_40) != iProver_top
% 0.88/1.02      | v1_funct_1(X0_40) != iProver_top
% 0.88/1.02      | v2_funct_1(X0_40) = iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1642,plain,
% 0.88/1.02      ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
% 0.88/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_1639,c_1067]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_573,plain,
% 0.88/1.02      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 0.88/1.02      | ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | k2_funct_1(sK2) != X0 ),
% 0.88/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_574,plain,
% 0.88/1.02      ( r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | ~ v1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(unflattening,[status(thm)],[c_573]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_575,plain,
% 0.88/1.02      ( r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) = iProver_top
% 0.88/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.88/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1453,plain,
% 0.88/1.02      ( sK0(k2_funct_1(sK2)) = sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_822]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1232,plain,
% 0.88/1.02      ( r2_hidden(X0_41,X0_42)
% 0.88/1.02      | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | X0_42 != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | X0_41 != sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_827]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1431,plain,
% 0.88/1.02      ( r2_hidden(X0_41,k2_relat_1(sK2))
% 0.88/1.02      | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | X0_41 != sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1232]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1502,plain,
% 0.88/1.02      ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2))
% 0.88/1.02      | ~ r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2)))
% 0.88/1.02      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | sK0(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_1431]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1504,plain,
% 0.88/1.02      ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | sK0(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2))
% 0.88/1.02      | r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top
% 0.88/1.02      | r2_hidden(sK0(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
% 0.88/1.02      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1663,plain,
% 0.88/1.02      ( r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2)) = iProver_top ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1642,c_14,c_15,c_13,c_16,c_12,c_33,c_36,c_575,c_844,
% 0.88/1.02                 c_1371,c_1372,c_1453,c_1504]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1856,plain,
% 0.88/1.02      ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2))
% 0.88/1.02      | v1_relat_1(sK2) != iProver_top
% 0.88/1.02      | v1_funct_1(sK2) != iProver_top
% 0.88/1.02      | v2_funct_1(sK2) != iProver_top ),
% 0.88/1.02      inference(superposition,[status(thm)],[c_1663,c_1074]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1537,plain,
% 0.88/1.02      ( ~ r2_hidden(sK0(k2_funct_1(sK2)),k2_relat_1(sK2))
% 0.88/1.02      | ~ v1_relat_1(sK2)
% 0.88/1.02      | ~ v1_funct_1(sK2)
% 0.88/1.02      | ~ v2_funct_1(sK2)
% 0.88/1.02      | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_810]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2063,plain,
% 0.88/1.02      ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK0(k2_funct_1(sK2)))) = sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(global_propositional_subsumption,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_1856,c_14,c_13,c_12,c_32,c_35,c_574,c_844,c_1371,
% 0.88/1.02                 c_1372,c_1453,c_1502,c_1537]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_2315,plain,
% 0.88/1.02      ( sK1(k2_funct_1(sK2)) = sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(light_normalisation,[status(thm)],[c_2314,c_2063]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_0,plain,
% 0.88/1.02      ( ~ v1_relat_1(X0)
% 0.88/1.02      | ~ v1_funct_1(X0)
% 0.88/1.02      | v2_funct_1(X0)
% 0.88/1.02      | sK1(X0) != sK0(X0) ),
% 0.88/1.02      inference(cnf_transformation,[],[f27]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_820,plain,
% 0.88/1.02      ( ~ v1_relat_1(X0_40)
% 0.88/1.02      | ~ v1_funct_1(X0_40)
% 0.88/1.02      | v2_funct_1(X0_40)
% 0.88/1.02      | sK1(X0_40) != sK0(X0_40) ),
% 0.88/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(c_1222,plain,
% 0.88/1.02      ( ~ v1_relat_1(k2_funct_1(sK2))
% 0.88/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.88/1.02      | v2_funct_1(k2_funct_1(sK2))
% 0.88/1.02      | sK1(k2_funct_1(sK2)) != sK0(k2_funct_1(sK2)) ),
% 0.88/1.02      inference(instantiation,[status(thm)],[c_820]) ).
% 0.88/1.02  
% 0.88/1.02  cnf(contradiction,plain,
% 0.88/1.02      ( $false ),
% 0.88/1.02      inference(minisat,
% 0.88/1.02                [status(thm)],
% 0.88/1.02                [c_2315,c_1222,c_35,c_32,c_11,c_13,c_14]) ).
% 0.88/1.02  
% 0.88/1.02  
% 0.88/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.88/1.02  
% 0.88/1.02  ------                               Statistics
% 0.88/1.02  
% 0.88/1.02  ------ General
% 0.88/1.02  
% 0.88/1.02  abstr_ref_over_cycles:                  0
% 0.88/1.02  abstr_ref_under_cycles:                 0
% 0.88/1.02  gc_basic_clause_elim:                   0
% 0.88/1.02  forced_gc_time:                         0
% 0.88/1.02  parsing_time:                           0.006
% 0.88/1.02  unif_index_cands_time:                  0.
% 0.88/1.02  unif_index_add_time:                    0.
% 0.88/1.02  orderings_time:                         0.
% 0.88/1.02  out_proof_time:                         0.013
% 0.88/1.02  total_time:                             0.095
% 0.88/1.02  num_of_symbols:                         46
% 0.88/1.02  num_of_terms:                           1224
% 0.88/1.02  
% 0.88/1.02  ------ Preprocessing
% 0.88/1.02  
% 0.88/1.02  num_of_splits:                          0
% 0.88/1.02  num_of_split_atoms:                     0
% 0.88/1.02  num_of_reused_defs:                     0
% 0.88/1.02  num_eq_ax_congr_red:                    14
% 0.88/1.02  num_of_sem_filtered_clauses:            1
% 0.88/1.02  num_of_subtypes:                        3
% 0.88/1.02  monotx_restored_types:                  0
% 0.88/1.02  sat_num_of_epr_types:                   0
% 0.88/1.02  sat_num_of_non_cyclic_types:            0
% 0.88/1.02  sat_guarded_non_collapsed_types:        1
% 0.88/1.02  num_pure_diseq_elim:                    0
% 0.88/1.02  simp_replaced_by:                       0
% 0.88/1.02  res_preprocessed:                       58
% 0.88/1.02  prep_upred:                             0
% 0.88/1.02  prep_unflattend:                        21
% 0.88/1.02  smt_new_axioms:                         0
% 0.88/1.02  pred_elim_cands:                        4
% 0.88/1.02  pred_elim:                              0
% 0.88/1.02  pred_elim_cl:                           0
% 0.88/1.02  pred_elim_cycles:                       1
% 0.88/1.02  merged_defs:                            0
% 0.88/1.02  merged_defs_ncl:                        0
% 0.88/1.02  bin_hyper_res:                          0
% 0.88/1.02  prep_cycles:                            3
% 0.88/1.02  pred_elim_time:                         0.012
% 0.88/1.02  splitting_time:                         0.
% 0.88/1.02  sem_filter_time:                        0.
% 0.88/1.02  monotx_time:                            0.
% 0.88/1.02  subtype_inf_time:                       0.
% 0.88/1.02  
% 0.88/1.02  ------ Problem properties
% 0.88/1.02  
% 0.88/1.02  clauses:                                15
% 0.88/1.02  conjectures:                            4
% 0.88/1.02  epr:                                    3
% 0.88/1.02  horn:                                   12
% 0.88/1.02  ground:                                 4
% 0.88/1.02  unary:                                  4
% 0.88/1.02  binary:                                 0
% 0.88/1.02  lits:                                   51
% 0.88/1.02  lits_eq:                                8
% 0.88/1.02  fd_pure:                                0
% 0.88/1.02  fd_pseudo:                              0
% 0.88/1.02  fd_cond:                                0
% 0.88/1.02  fd_pseudo_cond:                         1
% 0.88/1.02  ac_symbols:                             0
% 0.88/1.02  
% 0.88/1.02  ------ Propositional Solver
% 0.88/1.02  
% 0.88/1.02  prop_solver_calls:                      25
% 0.88/1.02  prop_fast_solver_calls:                 631
% 0.88/1.02  smt_solver_calls:                       0
% 0.88/1.02  smt_fast_solver_calls:                  0
% 0.88/1.02  prop_num_of_clauses:                    651
% 0.88/1.02  prop_preprocess_simplified:             2097
% 0.88/1.02  prop_fo_subsumed:                       45
% 0.88/1.02  prop_solver_time:                       0.
% 0.88/1.02  smt_solver_time:                        0.
% 0.88/1.02  smt_fast_solver_time:                   0.
% 0.88/1.02  prop_fast_solver_time:                  0.
% 0.88/1.02  prop_unsat_core_time:                   0.
% 0.88/1.02  
% 0.88/1.02  ------ QBF
% 0.88/1.02  
% 0.88/1.02  qbf_q_res:                              0
% 0.88/1.02  qbf_num_tautologies:                    0
% 0.88/1.02  qbf_prep_cycles:                        0
% 0.88/1.02  
% 0.88/1.02  ------ BMC1
% 0.88/1.02  
% 0.88/1.02  bmc1_current_bound:                     -1
% 0.88/1.02  bmc1_last_solved_bound:                 -1
% 0.88/1.02  bmc1_unsat_core_size:                   -1
% 0.88/1.02  bmc1_unsat_core_parents_size:           -1
% 0.88/1.02  bmc1_merge_next_fun:                    0
% 0.88/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.88/1.02  
% 0.88/1.02  ------ Instantiation
% 0.88/1.02  
% 0.88/1.02  inst_num_of_clauses:                    191
% 0.88/1.02  inst_num_in_passive:                    0
% 0.88/1.02  inst_num_in_active:                     131
% 0.88/1.02  inst_num_in_unprocessed:                60
% 0.88/1.02  inst_num_of_loops:                      140
% 0.88/1.02  inst_num_of_learning_restarts:          0
% 0.88/1.02  inst_num_moves_active_passive:          0
% 0.88/1.02  inst_lit_activity:                      0
% 0.88/1.02  inst_lit_activity_moves:                0
% 0.88/1.02  inst_num_tautologies:                   0
% 0.88/1.02  inst_num_prop_implied:                  0
% 0.88/1.02  inst_num_existing_simplified:           0
% 0.88/1.02  inst_num_eq_res_simplified:             0
% 0.88/1.02  inst_num_child_elim:                    0
% 0.88/1.02  inst_num_of_dismatching_blockings:      14
% 0.88/1.02  inst_num_of_non_proper_insts:           218
% 0.88/1.02  inst_num_of_duplicates:                 0
% 0.88/1.02  inst_inst_num_from_inst_to_res:         0
% 0.88/1.02  inst_dismatching_checking_time:         0.
% 0.88/1.02  
% 0.88/1.02  ------ Resolution
% 0.88/1.02  
% 0.88/1.02  res_num_of_clauses:                     0
% 0.88/1.02  res_num_in_passive:                     0
% 0.88/1.02  res_num_in_active:                      0
% 0.88/1.02  res_num_of_loops:                       61
% 0.88/1.02  res_forward_subset_subsumed:            45
% 0.88/1.02  res_backward_subset_subsumed:           0
% 0.88/1.02  res_forward_subsumed:                   0
% 0.88/1.02  res_backward_subsumed:                  0
% 0.88/1.02  res_forward_subsumption_resolution:     0
% 0.88/1.02  res_backward_subsumption_resolution:    0
% 0.88/1.02  res_clause_to_clause_subsumption:       69
% 0.88/1.02  res_orphan_elimination:                 0
% 0.88/1.02  res_tautology_del:                      29
% 0.88/1.02  res_num_eq_res_simplified:              0
% 0.88/1.02  res_num_sel_changes:                    0
% 0.88/1.02  res_moves_from_active_to_pass:          0
% 0.88/1.02  
% 0.88/1.02  ------ Superposition
% 0.88/1.02  
% 0.88/1.02  sup_time_total:                         0.
% 0.88/1.02  sup_time_generating:                    0.
% 0.88/1.02  sup_time_sim_full:                      0.
% 0.88/1.02  sup_time_sim_immed:                     0.
% 0.88/1.02  
% 0.88/1.02  sup_num_of_clauses:                     33
% 0.88/1.02  sup_num_in_active:                      25
% 0.88/1.02  sup_num_in_passive:                     8
% 0.88/1.02  sup_num_of_loops:                       26
% 0.88/1.02  sup_fw_superposition:                   15
% 0.88/1.02  sup_bw_superposition:                   10
% 0.88/1.02  sup_immediate_simplified:               4
% 0.88/1.02  sup_given_eliminated:                   0
% 0.88/1.02  comparisons_done:                       0
% 0.88/1.02  comparisons_avoided:                    0
% 0.88/1.02  
% 0.88/1.02  ------ Simplifications
% 0.88/1.02  
% 0.88/1.02  
% 0.88/1.02  sim_fw_subset_subsumed:                 3
% 0.88/1.02  sim_bw_subset_subsumed:                 0
% 0.88/1.02  sim_fw_subsumed:                        0
% 0.88/1.02  sim_bw_subsumed:                        0
% 0.88/1.02  sim_fw_subsumption_res:                 0
% 0.88/1.02  sim_bw_subsumption_res:                 0
% 0.88/1.02  sim_tautology_del:                      0
% 0.88/1.02  sim_eq_tautology_del:                   1
% 0.88/1.02  sim_eq_res_simp:                        0
% 0.88/1.02  sim_fw_demodulated:                     0
% 0.88/1.02  sim_bw_demodulated:                     1
% 0.88/1.02  sim_light_normalised:                   1
% 0.88/1.02  sim_joinable_taut:                      0
% 0.88/1.02  sim_joinable_simp:                      0
% 0.88/1.02  sim_ac_normalised:                      0
% 0.88/1.02  sim_smt_subsumption:                    0
% 0.88/1.02  
%------------------------------------------------------------------------------
