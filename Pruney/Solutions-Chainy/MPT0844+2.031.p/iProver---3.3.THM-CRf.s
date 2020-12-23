%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:14 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 192 expanded)
%              Number of clauses        :   58 (  82 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  229 ( 534 expanded)
%              Number of equality atoms :   91 ( 164 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2)
      & r1_xboole_0(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2)
    & r1_xboole_0(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f24])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_147,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_148,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_438,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_148])).

cnf(c_608,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_442,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_467,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_469,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_669,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_44,X0_45))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_670,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))
    | v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_672,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_448,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_674,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_734,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_469,c_672,c_674])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_439,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_607,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_443,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_xboole_0(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_604,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_xboole_0(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_444,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_xboole_0(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_603,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) = iProver_top
    | r1_xboole_0(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_445,plain,
    ( ~ r2_hidden(X0_47,X0_44)
    | ~ r2_hidden(X0_47,X1_44)
    | ~ r1_xboole_0(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_602,plain,
    ( r2_hidden(X0_47,X0_44) != iProver_top
    | r2_hidden(X0_47,X1_44) != iProver_top
    | r1_xboole_0(X1_44,X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_896,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X2_44) != iProver_top
    | r1_xboole_0(X1_44,X2_44) != iProver_top
    | r1_xboole_0(X0_44,X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_603,c_602])).

cnf(c_1099,plain,
    ( r1_xboole_0(X0_44,X1_44) != iProver_top
    | r1_xboole_0(X1_44,X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_896])).

cnf(c_1114,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_1099])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_441,plain,
    ( ~ r1_xboole_0(X0_44,X1_44)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(k7_relat_1(X0_43,X0_44),X1_44) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_606,plain,
    ( k7_relat_1(k7_relat_1(X0_43,X0_44),X1_44) = k1_xboole_0
    | r1_xboole_0(X0_44,X1_44) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_1193,plain,
    ( k7_relat_1(k7_relat_1(X0_43,sK3),sK2) = k1_xboole_0
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_606])).

cnf(c_1204,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_734,c_1193])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_162,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_11])).

cnf(c_163,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(unflattening,[status(thm)],[c_162])).

cnf(c_437,plain,
    ( ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | k7_relat_1(sK4,X0_44) = sK4 ),
    inference(subtyping,[status(esa)],[c_163])).

cnf(c_609,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | k7_relat_1(sK4,X0_44) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_468,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_671,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_781,plain,
    ( k7_relat_1(sK4,X0_44) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_468,c_437,c_671,c_674])).

cnf(c_782,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | k7_relat_1(sK4,X0_44) = sK4 ),
    inference(renaming,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_782])).

cnf(c_1209,plain,
    ( k7_relat_1(sK4,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1204,c_786])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_177,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_178,plain,
    ( k5_relset_1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_436,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
    | k5_relset_1(X0_44,X0_45,sK4,X1_44) = k7_relat_1(sK4,X1_44) ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_701,plain,
    ( k5_relset_1(sK3,sK1,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
    inference(equality_resolution,[status(thm)],[c_436])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_440,negated_conjecture,
    ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_704,plain,
    ( k7_relat_1(sK4,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_701,c_440])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1209,c_704])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.70/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.70/1.07  
% 0.70/1.07  ------  iProver source info
% 0.70/1.07  
% 0.70/1.07  git: date: 2020-06-30 10:37:57 +0100
% 0.70/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.70/1.07  git: non_committed_changes: false
% 0.70/1.07  git: last_make_outside_of_git: false
% 0.70/1.07  
% 0.70/1.07  ------ 
% 0.70/1.07  
% 0.70/1.07  ------ Input Options
% 0.70/1.07  
% 0.70/1.07  --out_options                           all
% 0.70/1.07  --tptp_safe_out                         true
% 0.70/1.07  --problem_path                          ""
% 0.70/1.07  --include_path                          ""
% 0.70/1.07  --clausifier                            res/vclausify_rel
% 0.70/1.07  --clausifier_options                    --mode clausify
% 0.70/1.07  --stdin                                 false
% 0.70/1.07  --stats_out                             all
% 0.70/1.07  
% 0.70/1.07  ------ General Options
% 0.70/1.07  
% 0.70/1.07  --fof                                   false
% 0.70/1.07  --time_out_real                         305.
% 0.70/1.07  --time_out_virtual                      -1.
% 0.70/1.07  --symbol_type_check                     false
% 0.70/1.07  --clausify_out                          false
% 0.70/1.07  --sig_cnt_out                           false
% 0.70/1.07  --trig_cnt_out                          false
% 0.70/1.07  --trig_cnt_out_tolerance                1.
% 0.70/1.07  --trig_cnt_out_sk_spl                   false
% 0.70/1.07  --abstr_cl_out                          false
% 0.70/1.07  
% 0.70/1.07  ------ Global Options
% 0.70/1.07  
% 0.70/1.07  --schedule                              default
% 0.70/1.07  --add_important_lit                     false
% 0.70/1.07  --prop_solver_per_cl                    1000
% 0.70/1.07  --min_unsat_core                        false
% 0.70/1.07  --soft_assumptions                      false
% 0.70/1.07  --soft_lemma_size                       3
% 0.70/1.07  --prop_impl_unit_size                   0
% 0.70/1.07  --prop_impl_unit                        []
% 0.70/1.07  --share_sel_clauses                     true
% 0.70/1.07  --reset_solvers                         false
% 0.70/1.07  --bc_imp_inh                            [conj_cone]
% 0.70/1.07  --conj_cone_tolerance                   3.
% 0.70/1.07  --extra_neg_conj                        none
% 0.70/1.07  --large_theory_mode                     true
% 0.70/1.07  --prolific_symb_bound                   200
% 0.70/1.07  --lt_threshold                          2000
% 0.70/1.07  --clause_weak_htbl                      true
% 0.70/1.07  --gc_record_bc_elim                     false
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing Options
% 0.70/1.07  
% 0.70/1.07  --preprocessing_flag                    true
% 0.70/1.07  --time_out_prep_mult                    0.1
% 0.70/1.07  --splitting_mode                        input
% 0.70/1.07  --splitting_grd                         true
% 0.70/1.07  --splitting_cvd                         false
% 0.70/1.07  --splitting_cvd_svl                     false
% 0.70/1.07  --splitting_nvd                         32
% 0.70/1.07  --sub_typing                            true
% 0.70/1.07  --prep_gs_sim                           true
% 0.70/1.07  --prep_unflatten                        true
% 0.70/1.07  --prep_res_sim                          true
% 0.70/1.07  --prep_upred                            true
% 0.70/1.07  --prep_sem_filter                       exhaustive
% 0.70/1.07  --prep_sem_filter_out                   false
% 0.70/1.07  --pred_elim                             true
% 0.70/1.07  --res_sim_input                         true
% 0.70/1.07  --eq_ax_congr_red                       true
% 0.70/1.07  --pure_diseq_elim                       true
% 0.70/1.07  --brand_transform                       false
% 0.70/1.07  --non_eq_to_eq                          false
% 0.70/1.07  --prep_def_merge                        true
% 0.70/1.07  --prep_def_merge_prop_impl              false
% 0.70/1.07  --prep_def_merge_mbd                    true
% 0.70/1.07  --prep_def_merge_tr_red                 false
% 0.70/1.07  --prep_def_merge_tr_cl                  false
% 0.70/1.07  --smt_preprocessing                     true
% 0.70/1.07  --smt_ac_axioms                         fast
% 0.70/1.07  --preprocessed_out                      false
% 0.70/1.07  --preprocessed_stats                    false
% 0.70/1.07  
% 0.70/1.07  ------ Abstraction refinement Options
% 0.70/1.07  
% 0.70/1.07  --abstr_ref                             []
% 0.70/1.07  --abstr_ref_prep                        false
% 0.70/1.07  --abstr_ref_until_sat                   false
% 0.70/1.07  --abstr_ref_sig_restrict                funpre
% 0.70/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.07  --abstr_ref_under                       []
% 0.70/1.07  
% 0.70/1.07  ------ SAT Options
% 0.70/1.07  
% 0.70/1.07  --sat_mode                              false
% 0.70/1.07  --sat_fm_restart_options                ""
% 0.70/1.07  --sat_gr_def                            false
% 0.70/1.07  --sat_epr_types                         true
% 0.70/1.07  --sat_non_cyclic_types                  false
% 0.70/1.07  --sat_finite_models                     false
% 0.70/1.07  --sat_fm_lemmas                         false
% 0.70/1.07  --sat_fm_prep                           false
% 0.70/1.07  --sat_fm_uc_incr                        true
% 0.70/1.07  --sat_out_model                         small
% 0.70/1.07  --sat_out_clauses                       false
% 0.70/1.07  
% 0.70/1.07  ------ QBF Options
% 0.70/1.07  
% 0.70/1.07  --qbf_mode                              false
% 0.70/1.07  --qbf_elim_univ                         false
% 0.70/1.07  --qbf_dom_inst                          none
% 0.70/1.07  --qbf_dom_pre_inst                      false
% 0.70/1.07  --qbf_sk_in                             false
% 0.70/1.07  --qbf_pred_elim                         true
% 0.70/1.07  --qbf_split                             512
% 0.70/1.07  
% 0.70/1.07  ------ BMC1 Options
% 0.70/1.07  
% 0.70/1.07  --bmc1_incremental                      false
% 0.70/1.07  --bmc1_axioms                           reachable_all
% 0.70/1.07  --bmc1_min_bound                        0
% 0.70/1.07  --bmc1_max_bound                        -1
% 0.70/1.07  --bmc1_max_bound_default                -1
% 0.70/1.07  --bmc1_symbol_reachability              true
% 0.70/1.07  --bmc1_property_lemmas                  false
% 0.70/1.07  --bmc1_k_induction                      false
% 0.70/1.07  --bmc1_non_equiv_states                 false
% 0.70/1.07  --bmc1_deadlock                         false
% 0.70/1.07  --bmc1_ucm                              false
% 0.70/1.07  --bmc1_add_unsat_core                   none
% 0.70/1.07  --bmc1_unsat_core_children              false
% 0.70/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.07  --bmc1_out_stat                         full
% 0.70/1.07  --bmc1_ground_init                      false
% 0.70/1.07  --bmc1_pre_inst_next_state              false
% 0.70/1.07  --bmc1_pre_inst_state                   false
% 0.70/1.07  --bmc1_pre_inst_reach_state             false
% 0.70/1.07  --bmc1_out_unsat_core                   false
% 0.70/1.07  --bmc1_aig_witness_out                  false
% 0.70/1.07  --bmc1_verbose                          false
% 0.70/1.07  --bmc1_dump_clauses_tptp                false
% 0.70/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.07  --bmc1_dump_file                        -
% 0.70/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.07  --bmc1_ucm_extend_mode                  1
% 0.70/1.07  --bmc1_ucm_init_mode                    2
% 0.70/1.07  --bmc1_ucm_cone_mode                    none
% 0.70/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.07  --bmc1_ucm_relax_model                  4
% 0.70/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.07  --bmc1_ucm_layered_model                none
% 0.70/1.07  --bmc1_ucm_max_lemma_size               10
% 0.70/1.07  
% 0.70/1.07  ------ AIG Options
% 0.70/1.07  
% 0.70/1.07  --aig_mode                              false
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation Options
% 0.70/1.07  
% 0.70/1.07  --instantiation_flag                    true
% 0.70/1.07  --inst_sos_flag                         false
% 0.70/1.07  --inst_sos_phase                        true
% 0.70/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel_side                     num_symb
% 0.70/1.07  --inst_solver_per_active                1400
% 0.70/1.07  --inst_solver_calls_frac                1.
% 0.70/1.07  --inst_passive_queue_type               priority_queues
% 0.70/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/1.07  --inst_passive_queues_freq              [25;2]
% 0.70/1.07  --inst_dismatching                      true
% 0.70/1.07  --inst_eager_unprocessed_to_passive     true
% 0.70/1.07  --inst_prop_sim_given                   true
% 0.70/1.07  --inst_prop_sim_new                     false
% 0.70/1.07  --inst_subs_new                         false
% 0.70/1.07  --inst_eq_res_simp                      false
% 0.70/1.07  --inst_subs_given                       false
% 0.70/1.07  --inst_orphan_elimination               true
% 0.70/1.07  --inst_learning_loop_flag               true
% 0.70/1.07  --inst_learning_start                   3000
% 0.70/1.07  --inst_learning_factor                  2
% 0.70/1.07  --inst_start_prop_sim_after_learn       3
% 0.70/1.07  --inst_sel_renew                        solver
% 0.70/1.07  --inst_lit_activity_flag                true
% 0.70/1.07  --inst_restr_to_given                   false
% 0.70/1.07  --inst_activity_threshold               500
% 0.70/1.07  --inst_out_proof                        true
% 0.70/1.07  
% 0.70/1.07  ------ Resolution Options
% 0.70/1.07  
% 0.70/1.07  --resolution_flag                       true
% 0.70/1.07  --res_lit_sel                           adaptive
% 0.70/1.07  --res_lit_sel_side                      none
% 0.70/1.07  --res_ordering                          kbo
% 0.70/1.07  --res_to_prop_solver                    active
% 0.70/1.07  --res_prop_simpl_new                    false
% 0.70/1.07  --res_prop_simpl_given                  true
% 0.70/1.07  --res_passive_queue_type                priority_queues
% 0.70/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.07  --res_passive_queues_freq               [15;5]
% 0.70/1.07  --res_forward_subs                      full
% 0.70/1.07  --res_backward_subs                     full
% 0.70/1.07  --res_forward_subs_resolution           true
% 0.70/1.07  --res_backward_subs_resolution          true
% 0.70/1.07  --res_orphan_elimination                true
% 0.70/1.07  --res_time_limit                        2.
% 0.70/1.07  --res_out_proof                         true
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Options
% 0.70/1.07  
% 0.70/1.07  --superposition_flag                    true
% 0.70/1.07  --sup_passive_queue_type                priority_queues
% 0.70/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.07  --demod_completeness_check              fast
% 0.70/1.07  --demod_use_ground                      true
% 0.70/1.07  --sup_to_prop_solver                    passive
% 0.70/1.07  --sup_prop_simpl_new                    true
% 0.70/1.07  --sup_prop_simpl_given                  true
% 0.70/1.07  --sup_fun_splitting                     false
% 0.70/1.07  --sup_smt_interval                      50000
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Simplification Setup
% 0.70/1.07  
% 0.70/1.07  --sup_indices_passive                   []
% 0.70/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_full_bw                           [BwDemod]
% 0.70/1.07  --sup_immed_triv                        [TrivRules]
% 0.70/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_immed_bw_main                     []
% 0.70/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  
% 0.70/1.07  ------ Combination Options
% 0.70/1.07  
% 0.70/1.07  --comb_res_mult                         3
% 0.70/1.07  --comb_sup_mult                         2
% 0.70/1.07  --comb_inst_mult                        10
% 0.70/1.07  
% 0.70/1.07  ------ Debug Options
% 0.70/1.07  
% 0.70/1.07  --dbg_backtrace                         false
% 0.70/1.07  --dbg_dump_prop_clauses                 false
% 0.70/1.07  --dbg_dump_prop_clauses_file            -
% 0.70/1.07  --dbg_out_stat                          false
% 0.70/1.07  ------ Parsing...
% 0.70/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.70/1.07  ------ Proving...
% 0.70/1.07  ------ Problem Properties 
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  clauses                                 10
% 0.70/1.07  conjectures                             2
% 0.70/1.07  EPR                                     2
% 0.70/1.07  Horn                                    8
% 0.70/1.07  unary                                   3
% 0.70/1.07  binary                                  3
% 0.70/1.07  lits                                    21
% 0.70/1.07  lits eq                                 7
% 0.70/1.07  fd_pure                                 0
% 0.70/1.07  fd_pseudo                               0
% 0.70/1.07  fd_cond                                 0
% 0.70/1.07  fd_pseudo_cond                          0
% 0.70/1.07  AC symbols                              0
% 0.70/1.07  
% 0.70/1.07  ------ Schedule dynamic 5 is on 
% 0.70/1.07  
% 0.70/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  ------ 
% 0.70/1.07  Current options:
% 0.70/1.07  ------ 
% 0.70/1.07  
% 0.70/1.07  ------ Input Options
% 0.70/1.07  
% 0.70/1.07  --out_options                           all
% 0.70/1.07  --tptp_safe_out                         true
% 0.70/1.07  --problem_path                          ""
% 0.70/1.07  --include_path                          ""
% 0.70/1.07  --clausifier                            res/vclausify_rel
% 0.70/1.07  --clausifier_options                    --mode clausify
% 0.70/1.07  --stdin                                 false
% 0.70/1.07  --stats_out                             all
% 0.70/1.07  
% 0.70/1.07  ------ General Options
% 0.70/1.07  
% 0.70/1.07  --fof                                   false
% 0.70/1.07  --time_out_real                         305.
% 0.70/1.07  --time_out_virtual                      -1.
% 0.70/1.07  --symbol_type_check                     false
% 0.70/1.07  --clausify_out                          false
% 0.70/1.07  --sig_cnt_out                           false
% 0.70/1.07  --trig_cnt_out                          false
% 0.70/1.07  --trig_cnt_out_tolerance                1.
% 0.70/1.07  --trig_cnt_out_sk_spl                   false
% 0.70/1.07  --abstr_cl_out                          false
% 0.70/1.07  
% 0.70/1.07  ------ Global Options
% 0.70/1.07  
% 0.70/1.07  --schedule                              default
% 0.70/1.07  --add_important_lit                     false
% 0.70/1.07  --prop_solver_per_cl                    1000
% 0.70/1.07  --min_unsat_core                        false
% 0.70/1.07  --soft_assumptions                      false
% 0.70/1.07  --soft_lemma_size                       3
% 0.70/1.07  --prop_impl_unit_size                   0
% 0.70/1.07  --prop_impl_unit                        []
% 0.70/1.07  --share_sel_clauses                     true
% 0.70/1.07  --reset_solvers                         false
% 0.70/1.07  --bc_imp_inh                            [conj_cone]
% 0.70/1.07  --conj_cone_tolerance                   3.
% 0.70/1.07  --extra_neg_conj                        none
% 0.70/1.07  --large_theory_mode                     true
% 0.70/1.07  --prolific_symb_bound                   200
% 0.70/1.07  --lt_threshold                          2000
% 0.70/1.07  --clause_weak_htbl                      true
% 0.70/1.07  --gc_record_bc_elim                     false
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing Options
% 0.70/1.07  
% 0.70/1.07  --preprocessing_flag                    true
% 0.70/1.07  --time_out_prep_mult                    0.1
% 0.70/1.07  --splitting_mode                        input
% 0.70/1.07  --splitting_grd                         true
% 0.70/1.07  --splitting_cvd                         false
% 0.70/1.07  --splitting_cvd_svl                     false
% 0.70/1.07  --splitting_nvd                         32
% 0.70/1.07  --sub_typing                            true
% 0.70/1.07  --prep_gs_sim                           true
% 0.70/1.07  --prep_unflatten                        true
% 0.70/1.07  --prep_res_sim                          true
% 0.70/1.07  --prep_upred                            true
% 0.70/1.07  --prep_sem_filter                       exhaustive
% 0.70/1.07  --prep_sem_filter_out                   false
% 0.70/1.07  --pred_elim                             true
% 0.70/1.07  --res_sim_input                         true
% 0.70/1.07  --eq_ax_congr_red                       true
% 0.70/1.07  --pure_diseq_elim                       true
% 0.70/1.07  --brand_transform                       false
% 0.70/1.07  --non_eq_to_eq                          false
% 0.70/1.07  --prep_def_merge                        true
% 0.70/1.07  --prep_def_merge_prop_impl              false
% 0.70/1.07  --prep_def_merge_mbd                    true
% 0.70/1.07  --prep_def_merge_tr_red                 false
% 0.70/1.07  --prep_def_merge_tr_cl                  false
% 0.70/1.07  --smt_preprocessing                     true
% 0.70/1.07  --smt_ac_axioms                         fast
% 0.70/1.07  --preprocessed_out                      false
% 0.70/1.07  --preprocessed_stats                    false
% 0.70/1.07  
% 0.70/1.07  ------ Abstraction refinement Options
% 0.70/1.07  
% 0.70/1.07  --abstr_ref                             []
% 0.70/1.07  --abstr_ref_prep                        false
% 0.70/1.07  --abstr_ref_until_sat                   false
% 0.70/1.07  --abstr_ref_sig_restrict                funpre
% 0.70/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.07  --abstr_ref_under                       []
% 0.70/1.07  
% 0.70/1.07  ------ SAT Options
% 0.70/1.07  
% 0.70/1.07  --sat_mode                              false
% 0.70/1.07  --sat_fm_restart_options                ""
% 0.70/1.07  --sat_gr_def                            false
% 0.70/1.07  --sat_epr_types                         true
% 0.70/1.07  --sat_non_cyclic_types                  false
% 0.70/1.07  --sat_finite_models                     false
% 0.70/1.07  --sat_fm_lemmas                         false
% 0.70/1.07  --sat_fm_prep                           false
% 0.70/1.07  --sat_fm_uc_incr                        true
% 0.70/1.07  --sat_out_model                         small
% 0.70/1.07  --sat_out_clauses                       false
% 0.70/1.07  
% 0.70/1.07  ------ QBF Options
% 0.70/1.07  
% 0.70/1.07  --qbf_mode                              false
% 0.70/1.07  --qbf_elim_univ                         false
% 0.70/1.07  --qbf_dom_inst                          none
% 0.70/1.07  --qbf_dom_pre_inst                      false
% 0.70/1.07  --qbf_sk_in                             false
% 0.70/1.07  --qbf_pred_elim                         true
% 0.70/1.07  --qbf_split                             512
% 0.70/1.07  
% 0.70/1.07  ------ BMC1 Options
% 0.70/1.07  
% 0.70/1.07  --bmc1_incremental                      false
% 0.70/1.07  --bmc1_axioms                           reachable_all
% 0.70/1.07  --bmc1_min_bound                        0
% 0.70/1.07  --bmc1_max_bound                        -1
% 0.70/1.07  --bmc1_max_bound_default                -1
% 0.70/1.07  --bmc1_symbol_reachability              true
% 0.70/1.07  --bmc1_property_lemmas                  false
% 0.70/1.07  --bmc1_k_induction                      false
% 0.70/1.07  --bmc1_non_equiv_states                 false
% 0.70/1.07  --bmc1_deadlock                         false
% 0.70/1.07  --bmc1_ucm                              false
% 0.70/1.07  --bmc1_add_unsat_core                   none
% 0.70/1.07  --bmc1_unsat_core_children              false
% 0.70/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.07  --bmc1_out_stat                         full
% 0.70/1.07  --bmc1_ground_init                      false
% 0.70/1.07  --bmc1_pre_inst_next_state              false
% 0.70/1.07  --bmc1_pre_inst_state                   false
% 0.70/1.07  --bmc1_pre_inst_reach_state             false
% 0.70/1.07  --bmc1_out_unsat_core                   false
% 0.70/1.07  --bmc1_aig_witness_out                  false
% 0.70/1.07  --bmc1_verbose                          false
% 0.70/1.07  --bmc1_dump_clauses_tptp                false
% 0.70/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.07  --bmc1_dump_file                        -
% 0.70/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.07  --bmc1_ucm_extend_mode                  1
% 0.70/1.07  --bmc1_ucm_init_mode                    2
% 0.70/1.07  --bmc1_ucm_cone_mode                    none
% 0.70/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.07  --bmc1_ucm_relax_model                  4
% 0.70/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.07  --bmc1_ucm_layered_model                none
% 0.70/1.07  --bmc1_ucm_max_lemma_size               10
% 0.70/1.07  
% 0.70/1.07  ------ AIG Options
% 0.70/1.07  
% 0.70/1.07  --aig_mode                              false
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation Options
% 0.70/1.07  
% 0.70/1.07  --instantiation_flag                    true
% 0.70/1.07  --inst_sos_flag                         false
% 0.70/1.07  --inst_sos_phase                        true
% 0.70/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/1.07  --inst_lit_sel_side                     none
% 0.70/1.07  --inst_solver_per_active                1400
% 0.70/1.07  --inst_solver_calls_frac                1.
% 0.70/1.07  --inst_passive_queue_type               priority_queues
% 0.70/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/1.07  --inst_passive_queues_freq              [25;2]
% 0.70/1.07  --inst_dismatching                      true
% 0.70/1.07  --inst_eager_unprocessed_to_passive     true
% 0.70/1.07  --inst_prop_sim_given                   true
% 0.70/1.07  --inst_prop_sim_new                     false
% 0.70/1.07  --inst_subs_new                         false
% 0.70/1.07  --inst_eq_res_simp                      false
% 0.70/1.07  --inst_subs_given                       false
% 0.70/1.07  --inst_orphan_elimination               true
% 0.70/1.07  --inst_learning_loop_flag               true
% 0.70/1.07  --inst_learning_start                   3000
% 0.70/1.07  --inst_learning_factor                  2
% 0.70/1.07  --inst_start_prop_sim_after_learn       3
% 0.70/1.07  --inst_sel_renew                        solver
% 0.70/1.07  --inst_lit_activity_flag                true
% 0.70/1.07  --inst_restr_to_given                   false
% 0.70/1.07  --inst_activity_threshold               500
% 0.70/1.07  --inst_out_proof                        true
% 0.70/1.07  
% 0.70/1.07  ------ Resolution Options
% 0.70/1.07  
% 0.70/1.07  --resolution_flag                       false
% 0.70/1.07  --res_lit_sel                           adaptive
% 0.70/1.07  --res_lit_sel_side                      none
% 0.70/1.07  --res_ordering                          kbo
% 0.70/1.07  --res_to_prop_solver                    active
% 0.70/1.07  --res_prop_simpl_new                    false
% 0.70/1.07  --res_prop_simpl_given                  true
% 0.70/1.07  --res_passive_queue_type                priority_queues
% 0.70/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.07  --res_passive_queues_freq               [15;5]
% 0.70/1.07  --res_forward_subs                      full
% 0.70/1.07  --res_backward_subs                     full
% 0.70/1.07  --res_forward_subs_resolution           true
% 0.70/1.07  --res_backward_subs_resolution          true
% 0.70/1.07  --res_orphan_elimination                true
% 0.70/1.07  --res_time_limit                        2.
% 0.70/1.07  --res_out_proof                         true
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Options
% 0.70/1.07  
% 0.70/1.07  --superposition_flag                    true
% 0.70/1.07  --sup_passive_queue_type                priority_queues
% 0.70/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.07  --demod_completeness_check              fast
% 0.70/1.07  --demod_use_ground                      true
% 0.70/1.07  --sup_to_prop_solver                    passive
% 0.70/1.07  --sup_prop_simpl_new                    true
% 0.70/1.07  --sup_prop_simpl_given                  true
% 0.70/1.07  --sup_fun_splitting                     false
% 0.70/1.07  --sup_smt_interval                      50000
% 0.70/1.07  
% 0.70/1.07  ------ Superposition Simplification Setup
% 0.70/1.07  
% 0.70/1.07  --sup_indices_passive                   []
% 0.70/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_full_bw                           [BwDemod]
% 0.70/1.07  --sup_immed_triv                        [TrivRules]
% 0.70/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_immed_bw_main                     []
% 0.70/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.07  
% 0.70/1.07  ------ Combination Options
% 0.70/1.07  
% 0.70/1.07  --comb_res_mult                         3
% 0.70/1.07  --comb_sup_mult                         2
% 0.70/1.07  --comb_inst_mult                        10
% 0.70/1.07  
% 0.70/1.07  ------ Debug Options
% 0.70/1.07  
% 0.70/1.07  --dbg_backtrace                         false
% 0.70/1.07  --dbg_dump_prop_clauses                 false
% 0.70/1.07  --dbg_dump_prop_clauses_file            -
% 0.70/1.07  --dbg_out_stat                          false
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  ------ Proving...
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  % SZS status Theorem for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  fof(f2,axiom,(
% 0.70/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f13,plain,(
% 0.70/1.07    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.70/1.07    inference(ennf_transformation,[],[f2])).
% 0.70/1.07  
% 0.70/1.07  fof(f29,plain,(
% 0.70/1.07    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f13])).
% 0.70/1.07  
% 0.70/1.07  fof(f8,conjecture,(
% 0.70/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f9,negated_conjecture,(
% 0.70/1.07    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.70/1.07    inference(negated_conjecture,[],[f8])).
% 0.70/1.07  
% 0.70/1.07  fof(f20,plain,(
% 0.70/1.07    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.70/1.07    inference(ennf_transformation,[],[f9])).
% 0.70/1.07  
% 0.70/1.07  fof(f21,plain,(
% 0.70/1.07    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.70/1.07    inference(flattening,[],[f20])).
% 0.70/1.07  
% 0.70/1.07  fof(f24,plain,(
% 0.70/1.07    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) & r1_xboole_0(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))))),
% 0.70/1.07    introduced(choice_axiom,[])).
% 0.70/1.07  
% 0.70/1.07  fof(f25,plain,(
% 0.70/1.07    k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) & r1_xboole_0(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.70/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f24])).
% 0.70/1.07  
% 0.70/1.07  fof(f35,plain,(
% 0.70/1.07    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.70/1.07    inference(cnf_transformation,[],[f25])).
% 0.70/1.07  
% 0.70/1.07  fof(f3,axiom,(
% 0.70/1.07    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f30,plain,(
% 0.70/1.07    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.70/1.07    inference(cnf_transformation,[],[f3])).
% 0.70/1.07  
% 0.70/1.07  fof(f36,plain,(
% 0.70/1.07    r1_xboole_0(sK2,sK3)),
% 0.70/1.07    inference(cnf_transformation,[],[f25])).
% 0.70/1.07  
% 0.70/1.07  fof(f1,axiom,(
% 0.70/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f10,plain,(
% 0.70/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.70/1.07    inference(rectify,[],[f1])).
% 0.70/1.07  
% 0.70/1.07  fof(f12,plain,(
% 0.70/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.70/1.07    inference(ennf_transformation,[],[f10])).
% 0.70/1.07  
% 0.70/1.07  fof(f22,plain,(
% 0.70/1.07    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.70/1.07    introduced(choice_axiom,[])).
% 0.70/1.07  
% 0.70/1.07  fof(f23,plain,(
% 0.70/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.70/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).
% 0.70/1.07  
% 0.70/1.07  fof(f26,plain,(
% 0.70/1.07    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f27,plain,(
% 0.70/1.07    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f28,plain,(
% 0.70/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f23])).
% 0.70/1.07  
% 0.70/1.07  fof(f4,axiom,(
% 0.70/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f14,plain,(
% 0.70/1.07    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.70/1.07    inference(ennf_transformation,[],[f4])).
% 0.70/1.07  
% 0.70/1.07  fof(f15,plain,(
% 0.70/1.07    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.70/1.07    inference(flattening,[],[f14])).
% 0.70/1.07  
% 0.70/1.07  fof(f31,plain,(
% 0.70/1.07    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f15])).
% 0.70/1.07  
% 0.70/1.07  fof(f6,axiom,(
% 0.70/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f11,plain,(
% 0.70/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.70/1.07    inference(pure_predicate_removal,[],[f6])).
% 0.70/1.07  
% 0.70/1.07  fof(f18,plain,(
% 0.70/1.07    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/1.07    inference(ennf_transformation,[],[f11])).
% 0.70/1.07  
% 0.70/1.07  fof(f33,plain,(
% 0.70/1.07    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.70/1.07    inference(cnf_transformation,[],[f18])).
% 0.70/1.07  
% 0.70/1.07  fof(f5,axiom,(
% 0.70/1.07    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f16,plain,(
% 0.70/1.07    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.70/1.07    inference(ennf_transformation,[],[f5])).
% 0.70/1.07  
% 0.70/1.07  fof(f17,plain,(
% 0.70/1.07    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.70/1.07    inference(flattening,[],[f16])).
% 0.70/1.07  
% 0.70/1.07  fof(f32,plain,(
% 0.70/1.07    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.70/1.07    inference(cnf_transformation,[],[f17])).
% 0.70/1.07  
% 0.70/1.07  fof(f7,axiom,(
% 0.70/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 0.70/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/1.07  
% 0.70/1.07  fof(f19,plain,(
% 0.70/1.07    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/1.07    inference(ennf_transformation,[],[f7])).
% 0.70/1.07  
% 0.70/1.07  fof(f34,plain,(
% 0.70/1.07    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.70/1.07    inference(cnf_transformation,[],[f19])).
% 0.70/1.07  
% 0.70/1.07  fof(f37,plain,(
% 0.70/1.07    k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2)),
% 0.70/1.07    inference(cnf_transformation,[],[f25])).
% 0.70/1.07  
% 0.70/1.07  cnf(c_3,plain,
% 0.70/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.70/1.07      | ~ v1_relat_1(X1)
% 0.70/1.07      | v1_relat_1(X0) ),
% 0.70/1.07      inference(cnf_transformation,[],[f29]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_11,negated_conjecture,
% 0.70/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 0.70/1.07      inference(cnf_transformation,[],[f35]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_147,plain,
% 0.70/1.07      ( ~ v1_relat_1(X0)
% 0.70/1.07      | v1_relat_1(X1)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0)
% 0.70/1.07      | sK4 != X1 ),
% 0.70/1.07      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_148,plain,
% 0.70/1.07      ( ~ v1_relat_1(X0)
% 0.70/1.07      | v1_relat_1(sK4)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0) ),
% 0.70/1.07      inference(unflattening,[status(thm)],[c_147]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_438,plain,
% 0.70/1.07      ( ~ v1_relat_1(X0_43)
% 0.70/1.07      | v1_relat_1(sK4)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0_43) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_148]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_608,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(X0_43)
% 0.70/1.07      | v1_relat_1(X0_43) != iProver_top
% 0.70/1.07      | v1_relat_1(sK4) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_4,plain,
% 0.70/1.07      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.70/1.07      inference(cnf_transformation,[],[f30]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_442,plain,
% 0.70/1.07      ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_4]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_467,plain,
% 0.70/1.07      ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_469,plain,
% 0.70/1.07      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_467]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_669,plain,
% 0.70/1.07      ( ~ v1_relat_1(k2_zfmisc_1(X0_44,X0_45))
% 0.70/1.07      | v1_relat_1(sK4)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_438]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_670,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))
% 0.70/1.07      | v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) != iProver_top
% 0.70/1.07      | v1_relat_1(sK4) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_672,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 0.70/1.07      | v1_relat_1(sK4) = iProver_top ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_670]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_448,plain,( X0_46 = X0_46 ),theory(equality) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_674,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_448]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_734,plain,
% 0.70/1.07      ( v1_relat_1(sK4) = iProver_top ),
% 0.70/1.07      inference(global_propositional_subsumption,
% 0.70/1.07                [status(thm)],
% 0.70/1.07                [c_608,c_469,c_672,c_674]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_10,negated_conjecture,
% 0.70/1.07      ( r1_xboole_0(sK2,sK3) ),
% 0.70/1.07      inference(cnf_transformation,[],[f36]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_439,negated_conjecture,
% 0.70/1.07      ( r1_xboole_0(sK2,sK3) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_10]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_607,plain,
% 0.70/1.07      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_2,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 0.70/1.07      inference(cnf_transformation,[],[f26]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_443,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_xboole_0(X0_44,X1_44) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_2]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_604,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 0.70/1.07      | r1_xboole_0(X0_44,X1_44) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 0.70/1.07      inference(cnf_transformation,[],[f27]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_444,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_xboole_0(X0_44,X1_44) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_1]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_603,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0_44,X1_44),X1_44) = iProver_top
% 0.70/1.07      | r1_xboole_0(X0_44,X1_44) = iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_0,plain,
% 0.70/1.07      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 0.70/1.07      inference(cnf_transformation,[],[f28]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_445,plain,
% 0.70/1.07      ( ~ r2_hidden(X0_47,X0_44)
% 0.70/1.07      | ~ r2_hidden(X0_47,X1_44)
% 0.70/1.07      | ~ r1_xboole_0(X0_44,X1_44) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_0]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_602,plain,
% 0.70/1.07      ( r2_hidden(X0_47,X0_44) != iProver_top
% 0.70/1.07      | r2_hidden(X0_47,X1_44) != iProver_top
% 0.70/1.07      | r1_xboole_0(X1_44,X0_44) != iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_896,plain,
% 0.70/1.07      ( r2_hidden(sK0(X0_44,X1_44),X2_44) != iProver_top
% 0.70/1.07      | r1_xboole_0(X1_44,X2_44) != iProver_top
% 0.70/1.07      | r1_xboole_0(X0_44,X1_44) = iProver_top ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_603,c_602]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1099,plain,
% 0.70/1.07      ( r1_xboole_0(X0_44,X1_44) != iProver_top
% 0.70/1.07      | r1_xboole_0(X1_44,X0_44) = iProver_top ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_604,c_896]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1114,plain,
% 0.70/1.07      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_607,c_1099]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_5,plain,
% 0.70/1.07      ( ~ r1_xboole_0(X0,X1)
% 0.70/1.07      | ~ v1_relat_1(X2)
% 0.70/1.07      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 0.70/1.07      inference(cnf_transformation,[],[f31]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_441,plain,
% 0.70/1.07      ( ~ r1_xboole_0(X0_44,X1_44)
% 0.70/1.07      | ~ v1_relat_1(X0_43)
% 0.70/1.07      | k7_relat_1(k7_relat_1(X0_43,X0_44),X1_44) = k1_xboole_0 ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_5]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_606,plain,
% 0.70/1.07      ( k7_relat_1(k7_relat_1(X0_43,X0_44),X1_44) = k1_xboole_0
% 0.70/1.07      | r1_xboole_0(X0_44,X1_44) != iProver_top
% 0.70/1.07      | v1_relat_1(X0_43) != iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1193,plain,
% 0.70/1.07      ( k7_relat_1(k7_relat_1(X0_43,sK3),sK2) = k1_xboole_0
% 0.70/1.07      | v1_relat_1(X0_43) != iProver_top ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_1114,c_606]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1204,plain,
% 0.70/1.07      ( k7_relat_1(k7_relat_1(sK4,sK3),sK2) = k1_xboole_0 ),
% 0.70/1.07      inference(superposition,[status(thm)],[c_734,c_1193]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_7,plain,
% 0.70/1.07      ( v4_relat_1(X0,X1)
% 0.70/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.70/1.07      inference(cnf_transformation,[],[f33]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_6,plain,
% 0.70/1.07      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.70/1.07      inference(cnf_transformation,[],[f32]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_129,plain,
% 0.70/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.70/1.07      | ~ v1_relat_1(X0)
% 0.70/1.07      | k7_relat_1(X0,X1) = X0 ),
% 0.70/1.07      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_162,plain,
% 0.70/1.07      ( ~ v1_relat_1(X0)
% 0.70/1.07      | k7_relat_1(X0,X1) = X0
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | sK4 != X0 ),
% 0.70/1.07      inference(resolution_lifted,[status(thm)],[c_129,c_11]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_163,plain,
% 0.70/1.07      ( ~ v1_relat_1(sK4)
% 0.70/1.07      | k7_relat_1(sK4,X0) = sK4
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(unflattening,[status(thm)],[c_162]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_437,plain,
% 0.70/1.07      ( ~ v1_relat_1(sK4)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | k7_relat_1(sK4,X0_44) = sK4 ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_163]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_609,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | k7_relat_1(sK4,X0_44) = sK4
% 0.70/1.07      | v1_relat_1(sK4) != iProver_top ),
% 0.70/1.07      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_468,plain,
% 0.70/1.07      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_442]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_671,plain,
% 0.70/1.07      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | v1_relat_1(sK4)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(instantiation,[status(thm)],[c_669]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_781,plain,
% 0.70/1.07      ( k7_relat_1(sK4,X0_44) = sK4
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(global_propositional_subsumption,
% 0.70/1.07                [status(thm)],
% 0.70/1.07                [c_609,c_468,c_437,c_671,c_674]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_782,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | k7_relat_1(sK4,X0_44) = sK4 ),
% 0.70/1.07      inference(renaming,[status(thm)],[c_781]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_786,plain,
% 0.70/1.07      ( k7_relat_1(sK4,sK3) = sK4 ),
% 0.70/1.07      inference(equality_resolution,[status(thm)],[c_782]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_1209,plain,
% 0.70/1.07      ( k7_relat_1(sK4,sK2) = k1_xboole_0 ),
% 0.70/1.07      inference(light_normalisation,[status(thm)],[c_1204,c_786]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_8,plain,
% 0.70/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.70/1.07      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.70/1.07      inference(cnf_transformation,[],[f34]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_177,plain,
% 0.70/1.07      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | sK4 != X2 ),
% 0.70/1.07      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_178,plain,
% 0.70/1.07      ( k5_relset_1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 0.70/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)) ),
% 0.70/1.07      inference(unflattening,[status(thm)],[c_177]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_436,plain,
% 0.70/1.07      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))
% 0.70/1.07      | k5_relset_1(X0_44,X0_45,sK4,X1_44) = k7_relat_1(sK4,X1_44) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_178]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_701,plain,
% 0.70/1.07      ( k5_relset_1(sK3,sK1,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
% 0.70/1.07      inference(equality_resolution,[status(thm)],[c_436]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_9,negated_conjecture,
% 0.70/1.07      ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) ),
% 0.70/1.07      inference(cnf_transformation,[],[f37]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_440,negated_conjecture,
% 0.70/1.07      ( k1_xboole_0 != k5_relset_1(sK3,sK1,sK4,sK2) ),
% 0.70/1.07      inference(subtyping,[status(esa)],[c_9]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(c_704,plain,
% 0.70/1.07      ( k7_relat_1(sK4,sK2) != k1_xboole_0 ),
% 0.70/1.07      inference(demodulation,[status(thm)],[c_701,c_440]) ).
% 0.70/1.07  
% 0.70/1.07  cnf(contradiction,plain,
% 0.70/1.07      ( $false ),
% 0.70/1.07      inference(minisat,[status(thm)],[c_1209,c_704]) ).
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 0.70/1.07  
% 0.70/1.07  ------                               Statistics
% 0.70/1.07  
% 0.70/1.07  ------ General
% 0.70/1.07  
% 0.70/1.07  abstr_ref_over_cycles:                  0
% 0.70/1.07  abstr_ref_under_cycles:                 0
% 0.70/1.07  gc_basic_clause_elim:                   0
% 0.70/1.07  forced_gc_time:                         0
% 0.70/1.07  parsing_time:                           0.006
% 0.70/1.07  unif_index_cands_time:                  0.
% 0.70/1.07  unif_index_add_time:                    0.
% 0.70/1.07  orderings_time:                         0.
% 0.70/1.07  out_proof_time:                         0.007
% 0.70/1.07  total_time:                             0.064
% 0.70/1.07  num_of_symbols:                         48
% 0.70/1.07  num_of_terms:                           1129
% 0.70/1.07  
% 0.70/1.07  ------ Preprocessing
% 0.70/1.07  
% 0.70/1.07  num_of_splits:                          0
% 0.70/1.07  num_of_split_atoms:                     0
% 0.70/1.07  num_of_reused_defs:                     0
% 0.70/1.07  num_eq_ax_congr_red:                    22
% 0.70/1.07  num_of_sem_filtered_clauses:            1
% 0.70/1.07  num_of_subtypes:                        5
% 0.70/1.07  monotx_restored_types:                  0
% 0.70/1.07  sat_num_of_epr_types:                   0
% 0.70/1.07  sat_num_of_non_cyclic_types:            0
% 0.70/1.07  sat_guarded_non_collapsed_types:        0
% 0.70/1.07  num_pure_diseq_elim:                    0
% 0.70/1.07  simp_replaced_by:                       0
% 0.70/1.07  res_preprocessed:                       59
% 0.70/1.07  prep_upred:                             0
% 0.70/1.07  prep_unflattend:                        19
% 0.70/1.07  smt_new_axioms:                         0
% 0.70/1.07  pred_elim_cands:                        3
% 0.70/1.07  pred_elim:                              2
% 0.70/1.07  pred_elim_cl:                           2
% 0.70/1.07  pred_elim_cycles:                       4
% 0.70/1.07  merged_defs:                            0
% 0.70/1.07  merged_defs_ncl:                        0
% 0.70/1.07  bin_hyper_res:                          0
% 0.70/1.07  prep_cycles:                            4
% 0.70/1.07  pred_elim_time:                         0.003
% 0.70/1.07  splitting_time:                         0.
% 0.70/1.07  sem_filter_time:                        0.
% 0.70/1.07  monotx_time:                            0.
% 0.70/1.07  subtype_inf_time:                       0.
% 0.70/1.07  
% 0.70/1.07  ------ Problem properties
% 0.70/1.07  
% 0.70/1.07  clauses:                                10
% 0.70/1.07  conjectures:                            2
% 0.70/1.07  epr:                                    2
% 0.70/1.07  horn:                                   8
% 0.70/1.07  ground:                                 2
% 0.70/1.07  unary:                                  3
% 0.70/1.07  binary:                                 3
% 0.70/1.07  lits:                                   21
% 0.70/1.07  lits_eq:                                7
% 0.70/1.07  fd_pure:                                0
% 0.70/1.07  fd_pseudo:                              0
% 0.70/1.07  fd_cond:                                0
% 0.70/1.07  fd_pseudo_cond:                         0
% 0.70/1.07  ac_symbols:                             0
% 0.70/1.07  
% 0.70/1.07  ------ Propositional Solver
% 0.70/1.07  
% 0.70/1.07  prop_solver_calls:                      28
% 0.70/1.07  prop_fast_solver_calls:                 326
% 0.70/1.07  smt_solver_calls:                       0
% 0.70/1.07  smt_fast_solver_calls:                  0
% 0.70/1.07  prop_num_of_clauses:                    379
% 0.70/1.07  prop_preprocess_simplified:             1910
% 0.70/1.07  prop_fo_subsumed:                       3
% 0.70/1.07  prop_solver_time:                       0.
% 0.70/1.07  smt_solver_time:                        0.
% 0.70/1.07  smt_fast_solver_time:                   0.
% 0.70/1.07  prop_fast_solver_time:                  0.
% 0.70/1.07  prop_unsat_core_time:                   0.
% 0.70/1.07  
% 0.70/1.07  ------ QBF
% 0.70/1.07  
% 0.70/1.07  qbf_q_res:                              0
% 0.70/1.07  qbf_num_tautologies:                    0
% 0.70/1.07  qbf_prep_cycles:                        0
% 0.70/1.07  
% 0.70/1.07  ------ BMC1
% 0.70/1.07  
% 0.70/1.07  bmc1_current_bound:                     -1
% 0.70/1.07  bmc1_last_solved_bound:                 -1
% 0.70/1.07  bmc1_unsat_core_size:                   -1
% 0.70/1.07  bmc1_unsat_core_parents_size:           -1
% 0.70/1.07  bmc1_merge_next_fun:                    0
% 0.70/1.07  bmc1_unsat_core_clauses_time:           0.
% 0.70/1.07  
% 0.70/1.07  ------ Instantiation
% 0.70/1.07  
% 0.70/1.07  inst_num_of_clauses:                    132
% 0.70/1.07  inst_num_in_passive:                    17
% 0.70/1.07  inst_num_in_active:                     90
% 0.70/1.07  inst_num_in_unprocessed:                26
% 0.70/1.07  inst_num_of_loops:                      100
% 0.70/1.07  inst_num_of_learning_restarts:          0
% 0.70/1.07  inst_num_moves_active_passive:          6
% 0.70/1.07  inst_lit_activity:                      0
% 0.70/1.07  inst_lit_activity_moves:                0
% 0.70/1.07  inst_num_tautologies:                   0
% 0.70/1.07  inst_num_prop_implied:                  0
% 0.70/1.07  inst_num_existing_simplified:           0
% 0.70/1.07  inst_num_eq_res_simplified:             0
% 0.70/1.07  inst_num_child_elim:                    0
% 0.70/1.07  inst_num_of_dismatching_blockings:      13
% 0.70/1.07  inst_num_of_non_proper_insts:           110
% 0.70/1.07  inst_num_of_duplicates:                 0
% 0.70/1.07  inst_inst_num_from_inst_to_res:         0
% 0.70/1.07  inst_dismatching_checking_time:         0.
% 0.70/1.07  
% 0.70/1.07  ------ Resolution
% 0.70/1.07  
% 0.70/1.07  res_num_of_clauses:                     0
% 0.70/1.07  res_num_in_passive:                     0
% 0.70/1.07  res_num_in_active:                      0
% 0.70/1.07  res_num_of_loops:                       63
% 0.70/1.07  res_forward_subset_subsumed:            20
% 0.70/1.07  res_backward_subset_subsumed:           4
% 0.70/1.07  res_forward_subsumed:                   0
% 0.70/1.07  res_backward_subsumed:                  0
% 0.70/1.07  res_forward_subsumption_resolution:     0
% 0.70/1.07  res_backward_subsumption_resolution:    0
% 0.70/1.07  res_clause_to_clause_subsumption:       37
% 0.70/1.07  res_orphan_elimination:                 0
% 0.70/1.07  res_tautology_del:                      19
% 0.70/1.07  res_num_eq_res_simplified:              0
% 0.70/1.07  res_num_sel_changes:                    0
% 0.70/1.07  res_moves_from_active_to_pass:          0
% 0.70/1.07  
% 0.70/1.07  ------ Superposition
% 0.70/1.07  
% 0.70/1.07  sup_time_total:                         0.
% 0.70/1.07  sup_time_generating:                    0.
% 0.70/1.07  sup_time_sim_full:                      0.
% 0.70/1.07  sup_time_sim_immed:                     0.
% 0.70/1.07  
% 0.70/1.07  sup_num_of_clauses:                     23
% 0.70/1.07  sup_num_in_active:                      19
% 0.70/1.07  sup_num_in_passive:                     4
% 0.70/1.07  sup_num_of_loops:                       19
% 0.70/1.07  sup_fw_superposition:                   8
% 0.70/1.07  sup_bw_superposition:                   4
% 0.70/1.07  sup_immediate_simplified:               1
% 0.70/1.07  sup_given_eliminated:                   0
% 0.70/1.07  comparisons_done:                       0
% 0.70/1.07  comparisons_avoided:                    0
% 0.70/1.07  
% 0.70/1.07  ------ Simplifications
% 0.70/1.07  
% 0.70/1.07  
% 0.70/1.07  sim_fw_subset_subsumed:                 0
% 0.70/1.07  sim_bw_subset_subsumed:                 0
% 0.70/1.07  sim_fw_subsumed:                        0
% 0.70/1.07  sim_bw_subsumed:                        0
% 0.70/1.07  sim_fw_subsumption_res:                 0
% 0.70/1.07  sim_bw_subsumption_res:                 0
% 0.70/1.07  sim_tautology_del:                      0
% 0.70/1.07  sim_eq_tautology_del:                   0
% 0.70/1.07  sim_eq_res_simp:                        0
% 0.70/1.07  sim_fw_demodulated:                     0
% 0.70/1.07  sim_bw_demodulated:                     1
% 0.70/1.07  sim_light_normalised:                   1
% 0.70/1.07  sim_joinable_taut:                      0
% 0.70/1.07  sim_joinable_simp:                      0
% 0.70/1.07  sim_ac_normalised:                      0
% 0.70/1.07  sim_smt_subsumption:                    0
% 0.70/1.07  
%------------------------------------------------------------------------------
