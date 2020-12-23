%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:53 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 861 expanded)
%              Number of clauses        :  117 ( 361 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   19
%              Number of atoms          :  485 (3984 expanded)
%              Number of equality atoms :  198 ( 751 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_495,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_827,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_825,plain,
    ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_1369,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_827,c_825])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_496,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1370,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1369,c_496])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X1_46)
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_819,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1114,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_827,c_819])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_968,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46)
    | ~ v1_relat_1(k2_zfmisc_1(X1_46,X2_46)) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1046,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_503,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1069,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1070,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_1171,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_23,c_1046,c_1070])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_316,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_317,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_319,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_20])).

cnf(c_490,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_832,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1178,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1171,c_832])).

cnf(c_1460,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1370,c_1178])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_492,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46)))
    | ~ m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46))
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_830,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46))) = iProver_top
    | m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_1916,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(X0_46)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_830])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_330,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_331,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_46,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_333,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_20,c_17,c_46])).

cnf(c_489,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_833,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1177,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1171,c_833])).

cnf(c_1940,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1916,c_1177])).

cnf(c_21,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_51,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_53,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_54,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_56,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_2395,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1940,c_21,c_23,c_53,c_56,c_1046,c_1070])).

cnf(c_13,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_223,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_224,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_224])).

cnf(c_287,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_491,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_831,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_1218,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1177,c_831])).

cnf(c_1308,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1218,c_21,c_23,c_53,c_56,c_1046,c_1070])).

cnf(c_1312,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1308,c_1178])).

cnf(c_1458,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1370,c_1312])).

cnf(c_1465,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1458])).

cnf(c_2403,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_1465])).

cnf(c_494,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_828,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_500,plain,
    ( ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X0_46)
    | v1_relat_1(k2_funct_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_823,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(k2_funct_1(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_502,plain,
    ( ~ v1_relat_1(X0_46)
    | k9_relat_1(X0_46,k1_relat_1(X0_46)) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_821,plain,
    ( k9_relat_1(X0_46,k1_relat_1(X0_46)) = k2_relat_1(X0_46)
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_1166,plain,
    ( k9_relat_1(k2_funct_1(X0_46),k1_relat_1(k2_funct_1(X0_46))) = k2_relat_1(k2_funct_1(X0_46))
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_821])).

cnf(c_1756,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_1166])).

cnf(c_1768,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK1) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1756,c_1177,c_1460])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_344,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_345,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_20])).

cnf(c_488,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_834,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1176,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46) ),
    inference(superposition,[status(thm)],[c_1171,c_834])).

cnf(c_1769,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1768,c_1176])).

cnf(c_1817,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_23,c_1046,c_1070])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k8_relset_1(X1_46,X2_46,X0_46,X3_46) = k10_relat_1(X0_46,X3_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_826,plain,
    ( k8_relset_1(X0_46,X1_46,X2_46,X3_46) = k10_relat_1(X2_46,X3_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_1474,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
    inference(superposition,[status(thm)],[c_827,c_826])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_824,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1618,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_824])).

cnf(c_1001,plain,
    ( m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_1002,plain,
    ( m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k8_relset_1(sK0,sK1,sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_507,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1098,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_508,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1160,plain,
    ( X0_46 != X1_46
    | X0_46 = k8_relset_1(sK0,sK1,sK2,X2_46)
    | k8_relset_1(sK0,sK1,sK2,X2_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1272,plain,
    ( X0_46 = k8_relset_1(sK0,sK1,sK2,X1_46)
    | X0_46 != k10_relat_1(sK2,X1_46)
    | k8_relset_1(sK0,sK1,sK2,X1_46) != k10_relat_1(sK2,X1_46) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_1295,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_46) != k10_relat_1(sK2,X0_46)
    | k10_relat_1(sK2,X0_46) = k8_relset_1(sK0,sK1,sK2,X0_46)
    | k10_relat_1(sK2,X0_46) != k10_relat_1(sK2,X0_46) ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_506,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1296,plain,
    ( k10_relat_1(sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1017,plain,
    ( m1_subset_1(X0_46,X0_47)
    | ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X1_46),k1_zfmisc_1(sK0))
    | X0_47 != k1_zfmisc_1(sK0)
    | X0_46 != k8_relset_1(sK0,sK1,sK2,X1_46) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1097,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X1_46),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
    | X0_46 != k8_relset_1(sK0,sK1,sK2,X1_46) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1580,plain,
    ( ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0))
    | m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
    | k10_relat_1(sK2,X0_46) != k8_relset_1(sK0,sK1,sK2,X0_46) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1581,plain,
    ( k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
    | k10_relat_1(sK2,X0_46) != k8_relset_1(sK0,sK1,sK2,X0_46)
    | m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_1623,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1618,c_18,c_23,c_1002,c_1006,c_1098,c_1295,c_1296,c_1581])).

cnf(c_1821,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_1623])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2403,c_1821])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:48:36 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.31/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/0.97  
% 2.31/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/0.97  
% 2.31/0.97  ------  iProver source info
% 2.31/0.97  
% 2.31/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.31/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/0.97  git: non_committed_changes: false
% 2.31/0.97  git: last_make_outside_of_git: false
% 2.31/0.97  
% 2.31/0.97  ------ 
% 2.31/0.97  
% 2.31/0.97  ------ Input Options
% 2.31/0.97  
% 2.31/0.97  --out_options                           all
% 2.31/0.97  --tptp_safe_out                         true
% 2.31/0.97  --problem_path                          ""
% 2.31/0.97  --include_path                          ""
% 2.31/0.97  --clausifier                            res/vclausify_rel
% 2.31/0.97  --clausifier_options                    --mode clausify
% 2.31/0.97  --stdin                                 false
% 2.31/0.97  --stats_out                             all
% 2.31/0.97  
% 2.31/0.97  ------ General Options
% 2.31/0.97  
% 2.31/0.97  --fof                                   false
% 2.31/0.97  --time_out_real                         305.
% 2.31/0.97  --time_out_virtual                      -1.
% 2.31/0.97  --symbol_type_check                     false
% 2.31/0.97  --clausify_out                          false
% 2.31/0.97  --sig_cnt_out                           false
% 2.31/0.97  --trig_cnt_out                          false
% 2.31/0.97  --trig_cnt_out_tolerance                1.
% 2.31/0.97  --trig_cnt_out_sk_spl                   false
% 2.31/0.97  --abstr_cl_out                          false
% 2.31/0.97  
% 2.31/0.97  ------ Global Options
% 2.31/0.97  
% 2.31/0.97  --schedule                              default
% 2.31/0.97  --add_important_lit                     false
% 2.31/0.97  --prop_solver_per_cl                    1000
% 2.31/0.97  --min_unsat_core                        false
% 2.31/0.97  --soft_assumptions                      false
% 2.31/0.97  --soft_lemma_size                       3
% 2.31/0.97  --prop_impl_unit_size                   0
% 2.31/0.97  --prop_impl_unit                        []
% 2.31/0.97  --share_sel_clauses                     true
% 2.31/0.97  --reset_solvers                         false
% 2.31/0.97  --bc_imp_inh                            [conj_cone]
% 2.31/0.97  --conj_cone_tolerance                   3.
% 2.31/0.97  --extra_neg_conj                        none
% 2.31/0.97  --large_theory_mode                     true
% 2.31/0.97  --prolific_symb_bound                   200
% 2.31/0.97  --lt_threshold                          2000
% 2.31/0.97  --clause_weak_htbl                      true
% 2.31/0.97  --gc_record_bc_elim                     false
% 2.31/0.97  
% 2.31/0.97  ------ Preprocessing Options
% 2.31/0.97  
% 2.31/0.97  --preprocessing_flag                    true
% 2.31/0.97  --time_out_prep_mult                    0.1
% 2.31/0.97  --splitting_mode                        input
% 2.31/0.97  --splitting_grd                         true
% 2.31/0.97  --splitting_cvd                         false
% 2.31/0.97  --splitting_cvd_svl                     false
% 2.31/0.97  --splitting_nvd                         32
% 2.31/0.97  --sub_typing                            true
% 2.31/0.97  --prep_gs_sim                           true
% 2.31/0.97  --prep_unflatten                        true
% 2.31/0.97  --prep_res_sim                          true
% 2.31/0.97  --prep_upred                            true
% 2.31/0.97  --prep_sem_filter                       exhaustive
% 2.31/0.97  --prep_sem_filter_out                   false
% 2.31/0.97  --pred_elim                             true
% 2.31/0.97  --res_sim_input                         true
% 2.31/0.97  --eq_ax_congr_red                       true
% 2.31/0.97  --pure_diseq_elim                       true
% 2.31/0.97  --brand_transform                       false
% 2.31/0.97  --non_eq_to_eq                          false
% 2.31/0.97  --prep_def_merge                        true
% 2.31/0.97  --prep_def_merge_prop_impl              false
% 2.31/0.97  --prep_def_merge_mbd                    true
% 2.31/0.97  --prep_def_merge_tr_red                 false
% 2.31/0.97  --prep_def_merge_tr_cl                  false
% 2.31/0.97  --smt_preprocessing                     true
% 2.31/0.97  --smt_ac_axioms                         fast
% 2.31/0.97  --preprocessed_out                      false
% 2.31/0.97  --preprocessed_stats                    false
% 2.31/0.97  
% 2.31/0.97  ------ Abstraction refinement Options
% 2.31/0.97  
% 2.31/0.97  --abstr_ref                             []
% 2.31/0.97  --abstr_ref_prep                        false
% 2.31/0.97  --abstr_ref_until_sat                   false
% 2.31/0.97  --abstr_ref_sig_restrict                funpre
% 2.31/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.97  --abstr_ref_under                       []
% 2.31/0.97  
% 2.31/0.97  ------ SAT Options
% 2.31/0.97  
% 2.31/0.97  --sat_mode                              false
% 2.31/0.97  --sat_fm_restart_options                ""
% 2.31/0.97  --sat_gr_def                            false
% 2.31/0.97  --sat_epr_types                         true
% 2.31/0.97  --sat_non_cyclic_types                  false
% 2.31/0.97  --sat_finite_models                     false
% 2.31/0.97  --sat_fm_lemmas                         false
% 2.31/0.97  --sat_fm_prep                           false
% 2.31/0.97  --sat_fm_uc_incr                        true
% 2.31/0.97  --sat_out_model                         small
% 2.31/0.97  --sat_out_clauses                       false
% 2.31/0.97  
% 2.31/0.97  ------ QBF Options
% 2.31/0.97  
% 2.31/0.97  --qbf_mode                              false
% 2.31/0.97  --qbf_elim_univ                         false
% 2.31/0.97  --qbf_dom_inst                          none
% 2.31/0.97  --qbf_dom_pre_inst                      false
% 2.31/0.97  --qbf_sk_in                             false
% 2.31/0.97  --qbf_pred_elim                         true
% 2.31/0.97  --qbf_split                             512
% 2.31/0.97  
% 2.31/0.97  ------ BMC1 Options
% 2.31/0.97  
% 2.31/0.97  --bmc1_incremental                      false
% 2.31/0.97  --bmc1_axioms                           reachable_all
% 2.31/0.97  --bmc1_min_bound                        0
% 2.31/0.97  --bmc1_max_bound                        -1
% 2.31/0.97  --bmc1_max_bound_default                -1
% 2.31/0.97  --bmc1_symbol_reachability              true
% 2.31/0.97  --bmc1_property_lemmas                  false
% 2.31/0.97  --bmc1_k_induction                      false
% 2.31/0.97  --bmc1_non_equiv_states                 false
% 2.31/0.97  --bmc1_deadlock                         false
% 2.31/0.97  --bmc1_ucm                              false
% 2.31/0.97  --bmc1_add_unsat_core                   none
% 2.31/0.97  --bmc1_unsat_core_children              false
% 2.31/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.97  --bmc1_out_stat                         full
% 2.31/0.97  --bmc1_ground_init                      false
% 2.31/0.97  --bmc1_pre_inst_next_state              false
% 2.31/0.97  --bmc1_pre_inst_state                   false
% 2.31/0.97  --bmc1_pre_inst_reach_state             false
% 2.31/0.97  --bmc1_out_unsat_core                   false
% 2.31/0.97  --bmc1_aig_witness_out                  false
% 2.31/0.97  --bmc1_verbose                          false
% 2.31/0.97  --bmc1_dump_clauses_tptp                false
% 2.31/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.97  --bmc1_dump_file                        -
% 2.31/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.97  --bmc1_ucm_extend_mode                  1
% 2.31/0.97  --bmc1_ucm_init_mode                    2
% 2.31/0.97  --bmc1_ucm_cone_mode                    none
% 2.31/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.97  --bmc1_ucm_relax_model                  4
% 2.31/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.97  --bmc1_ucm_layered_model                none
% 2.31/0.97  --bmc1_ucm_max_lemma_size               10
% 2.31/0.97  
% 2.31/0.97  ------ AIG Options
% 2.31/0.97  
% 2.31/0.97  --aig_mode                              false
% 2.31/0.97  
% 2.31/0.97  ------ Instantiation Options
% 2.31/0.97  
% 2.31/0.97  --instantiation_flag                    true
% 2.31/0.97  --inst_sos_flag                         false
% 2.31/0.97  --inst_sos_phase                        true
% 2.31/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.97  --inst_lit_sel_side                     num_symb
% 2.31/0.97  --inst_solver_per_active                1400
% 2.31/0.97  --inst_solver_calls_frac                1.
% 2.31/0.97  --inst_passive_queue_type               priority_queues
% 2.31/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.97  --inst_passive_queues_freq              [25;2]
% 2.31/0.97  --inst_dismatching                      true
% 2.31/0.97  --inst_eager_unprocessed_to_passive     true
% 2.31/0.97  --inst_prop_sim_given                   true
% 2.31/0.97  --inst_prop_sim_new                     false
% 2.31/0.97  --inst_subs_new                         false
% 2.31/0.97  --inst_eq_res_simp                      false
% 2.31/0.97  --inst_subs_given                       false
% 2.31/0.97  --inst_orphan_elimination               true
% 2.31/0.97  --inst_learning_loop_flag               true
% 2.31/0.97  --inst_learning_start                   3000
% 2.31/0.97  --inst_learning_factor                  2
% 2.31/0.97  --inst_start_prop_sim_after_learn       3
% 2.31/0.97  --inst_sel_renew                        solver
% 2.31/0.97  --inst_lit_activity_flag                true
% 2.31/0.97  --inst_restr_to_given                   false
% 2.31/0.97  --inst_activity_threshold               500
% 2.31/0.97  --inst_out_proof                        true
% 2.31/0.97  
% 2.31/0.97  ------ Resolution Options
% 2.31/0.97  
% 2.31/0.97  --resolution_flag                       true
% 2.31/0.97  --res_lit_sel                           adaptive
% 2.31/0.97  --res_lit_sel_side                      none
% 2.31/0.97  --res_ordering                          kbo
% 2.31/0.97  --res_to_prop_solver                    active
% 2.31/0.97  --res_prop_simpl_new                    false
% 2.31/0.97  --res_prop_simpl_given                  true
% 2.31/0.97  --res_passive_queue_type                priority_queues
% 2.31/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.97  --res_passive_queues_freq               [15;5]
% 2.31/0.97  --res_forward_subs                      full
% 2.31/0.97  --res_backward_subs                     full
% 2.31/0.97  --res_forward_subs_resolution           true
% 2.31/0.97  --res_backward_subs_resolution          true
% 2.31/0.97  --res_orphan_elimination                true
% 2.31/0.97  --res_time_limit                        2.
% 2.31/0.97  --res_out_proof                         true
% 2.31/0.97  
% 2.31/0.97  ------ Superposition Options
% 2.31/0.97  
% 2.31/0.97  --superposition_flag                    true
% 2.31/0.97  --sup_passive_queue_type                priority_queues
% 2.31/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.97  --demod_completeness_check              fast
% 2.31/0.97  --demod_use_ground                      true
% 2.31/0.97  --sup_to_prop_solver                    passive
% 2.31/0.97  --sup_prop_simpl_new                    true
% 2.31/0.97  --sup_prop_simpl_given                  true
% 2.31/0.97  --sup_fun_splitting                     false
% 2.31/0.97  --sup_smt_interval                      50000
% 2.31/0.97  
% 2.31/0.97  ------ Superposition Simplification Setup
% 2.31/0.97  
% 2.31/0.97  --sup_indices_passive                   []
% 2.31/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_full_bw                           [BwDemod]
% 2.31/0.97  --sup_immed_triv                        [TrivRules]
% 2.31/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_immed_bw_main                     []
% 2.31/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.97  
% 2.31/0.97  ------ Combination Options
% 2.31/0.97  
% 2.31/0.97  --comb_res_mult                         3
% 2.31/0.97  --comb_sup_mult                         2
% 2.31/0.97  --comb_inst_mult                        10
% 2.31/0.97  
% 2.31/0.97  ------ Debug Options
% 2.31/0.97  
% 2.31/0.97  --dbg_backtrace                         false
% 2.31/0.97  --dbg_dump_prop_clauses                 false
% 2.31/0.97  --dbg_dump_prop_clauses_file            -
% 2.31/0.97  --dbg_out_stat                          false
% 2.31/0.97  ------ Parsing...
% 2.31/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/0.97  
% 2.31/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.31/0.97  
% 2.31/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/0.97  
% 2.31/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/0.97  ------ Proving...
% 2.31/0.97  ------ Problem Properties 
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  clauses                                 17
% 2.31/0.97  conjectures                             3
% 2.31/0.97  EPR                                     1
% 2.31/0.97  Horn                                    17
% 2.31/0.97  unary                                   4
% 2.31/0.97  binary                                  7
% 2.31/0.97  lits                                    40
% 2.31/0.97  lits eq                                 10
% 2.31/0.97  fd_pure                                 0
% 2.31/0.97  fd_pseudo                               0
% 2.31/0.97  fd_cond                                 0
% 2.31/0.97  fd_pseudo_cond                          0
% 2.31/0.97  AC symbols                              0
% 2.31/0.97  
% 2.31/0.97  ------ Schedule dynamic 5 is on 
% 2.31/0.97  
% 2.31/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  ------ 
% 2.31/0.97  Current options:
% 2.31/0.97  ------ 
% 2.31/0.97  
% 2.31/0.97  ------ Input Options
% 2.31/0.97  
% 2.31/0.97  --out_options                           all
% 2.31/0.97  --tptp_safe_out                         true
% 2.31/0.97  --problem_path                          ""
% 2.31/0.97  --include_path                          ""
% 2.31/0.97  --clausifier                            res/vclausify_rel
% 2.31/0.97  --clausifier_options                    --mode clausify
% 2.31/0.97  --stdin                                 false
% 2.31/0.97  --stats_out                             all
% 2.31/0.97  
% 2.31/0.97  ------ General Options
% 2.31/0.97  
% 2.31/0.97  --fof                                   false
% 2.31/0.97  --time_out_real                         305.
% 2.31/0.97  --time_out_virtual                      -1.
% 2.31/0.97  --symbol_type_check                     false
% 2.31/0.97  --clausify_out                          false
% 2.31/0.97  --sig_cnt_out                           false
% 2.31/0.97  --trig_cnt_out                          false
% 2.31/0.97  --trig_cnt_out_tolerance                1.
% 2.31/0.97  --trig_cnt_out_sk_spl                   false
% 2.31/0.97  --abstr_cl_out                          false
% 2.31/0.97  
% 2.31/0.97  ------ Global Options
% 2.31/0.97  
% 2.31/0.97  --schedule                              default
% 2.31/0.97  --add_important_lit                     false
% 2.31/0.97  --prop_solver_per_cl                    1000
% 2.31/0.97  --min_unsat_core                        false
% 2.31/0.97  --soft_assumptions                      false
% 2.31/0.97  --soft_lemma_size                       3
% 2.31/0.97  --prop_impl_unit_size                   0
% 2.31/0.97  --prop_impl_unit                        []
% 2.31/0.97  --share_sel_clauses                     true
% 2.31/0.97  --reset_solvers                         false
% 2.31/0.97  --bc_imp_inh                            [conj_cone]
% 2.31/0.97  --conj_cone_tolerance                   3.
% 2.31/0.97  --extra_neg_conj                        none
% 2.31/0.97  --large_theory_mode                     true
% 2.31/0.97  --prolific_symb_bound                   200
% 2.31/0.97  --lt_threshold                          2000
% 2.31/0.97  --clause_weak_htbl                      true
% 2.31/0.97  --gc_record_bc_elim                     false
% 2.31/0.97  
% 2.31/0.97  ------ Preprocessing Options
% 2.31/0.97  
% 2.31/0.97  --preprocessing_flag                    true
% 2.31/0.97  --time_out_prep_mult                    0.1
% 2.31/0.97  --splitting_mode                        input
% 2.31/0.97  --splitting_grd                         true
% 2.31/0.97  --splitting_cvd                         false
% 2.31/0.97  --splitting_cvd_svl                     false
% 2.31/0.97  --splitting_nvd                         32
% 2.31/0.97  --sub_typing                            true
% 2.31/0.97  --prep_gs_sim                           true
% 2.31/0.97  --prep_unflatten                        true
% 2.31/0.97  --prep_res_sim                          true
% 2.31/0.97  --prep_upred                            true
% 2.31/0.97  --prep_sem_filter                       exhaustive
% 2.31/0.97  --prep_sem_filter_out                   false
% 2.31/0.97  --pred_elim                             true
% 2.31/0.97  --res_sim_input                         true
% 2.31/0.97  --eq_ax_congr_red                       true
% 2.31/0.97  --pure_diseq_elim                       true
% 2.31/0.97  --brand_transform                       false
% 2.31/0.97  --non_eq_to_eq                          false
% 2.31/0.97  --prep_def_merge                        true
% 2.31/0.97  --prep_def_merge_prop_impl              false
% 2.31/0.97  --prep_def_merge_mbd                    true
% 2.31/0.97  --prep_def_merge_tr_red                 false
% 2.31/0.97  --prep_def_merge_tr_cl                  false
% 2.31/0.97  --smt_preprocessing                     true
% 2.31/0.97  --smt_ac_axioms                         fast
% 2.31/0.97  --preprocessed_out                      false
% 2.31/0.97  --preprocessed_stats                    false
% 2.31/0.97  
% 2.31/0.97  ------ Abstraction refinement Options
% 2.31/0.97  
% 2.31/0.97  --abstr_ref                             []
% 2.31/0.97  --abstr_ref_prep                        false
% 2.31/0.97  --abstr_ref_until_sat                   false
% 2.31/0.97  --abstr_ref_sig_restrict                funpre
% 2.31/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.97  --abstr_ref_under                       []
% 2.31/0.97  
% 2.31/0.97  ------ SAT Options
% 2.31/0.97  
% 2.31/0.97  --sat_mode                              false
% 2.31/0.97  --sat_fm_restart_options                ""
% 2.31/0.97  --sat_gr_def                            false
% 2.31/0.97  --sat_epr_types                         true
% 2.31/0.97  --sat_non_cyclic_types                  false
% 2.31/0.97  --sat_finite_models                     false
% 2.31/0.97  --sat_fm_lemmas                         false
% 2.31/0.97  --sat_fm_prep                           false
% 2.31/0.97  --sat_fm_uc_incr                        true
% 2.31/0.97  --sat_out_model                         small
% 2.31/0.97  --sat_out_clauses                       false
% 2.31/0.97  
% 2.31/0.97  ------ QBF Options
% 2.31/0.97  
% 2.31/0.97  --qbf_mode                              false
% 2.31/0.97  --qbf_elim_univ                         false
% 2.31/0.97  --qbf_dom_inst                          none
% 2.31/0.97  --qbf_dom_pre_inst                      false
% 2.31/0.97  --qbf_sk_in                             false
% 2.31/0.97  --qbf_pred_elim                         true
% 2.31/0.97  --qbf_split                             512
% 2.31/0.97  
% 2.31/0.97  ------ BMC1 Options
% 2.31/0.97  
% 2.31/0.97  --bmc1_incremental                      false
% 2.31/0.97  --bmc1_axioms                           reachable_all
% 2.31/0.97  --bmc1_min_bound                        0
% 2.31/0.97  --bmc1_max_bound                        -1
% 2.31/0.97  --bmc1_max_bound_default                -1
% 2.31/0.97  --bmc1_symbol_reachability              true
% 2.31/0.97  --bmc1_property_lemmas                  false
% 2.31/0.97  --bmc1_k_induction                      false
% 2.31/0.97  --bmc1_non_equiv_states                 false
% 2.31/0.97  --bmc1_deadlock                         false
% 2.31/0.97  --bmc1_ucm                              false
% 2.31/0.97  --bmc1_add_unsat_core                   none
% 2.31/0.97  --bmc1_unsat_core_children              false
% 2.31/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.97  --bmc1_out_stat                         full
% 2.31/0.97  --bmc1_ground_init                      false
% 2.31/0.97  --bmc1_pre_inst_next_state              false
% 2.31/0.97  --bmc1_pre_inst_state                   false
% 2.31/0.97  --bmc1_pre_inst_reach_state             false
% 2.31/0.97  --bmc1_out_unsat_core                   false
% 2.31/0.97  --bmc1_aig_witness_out                  false
% 2.31/0.97  --bmc1_verbose                          false
% 2.31/0.97  --bmc1_dump_clauses_tptp                false
% 2.31/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.97  --bmc1_dump_file                        -
% 2.31/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.97  --bmc1_ucm_extend_mode                  1
% 2.31/0.97  --bmc1_ucm_init_mode                    2
% 2.31/0.97  --bmc1_ucm_cone_mode                    none
% 2.31/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.97  --bmc1_ucm_relax_model                  4
% 2.31/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.97  --bmc1_ucm_layered_model                none
% 2.31/0.97  --bmc1_ucm_max_lemma_size               10
% 2.31/0.97  
% 2.31/0.97  ------ AIG Options
% 2.31/0.97  
% 2.31/0.97  --aig_mode                              false
% 2.31/0.97  
% 2.31/0.97  ------ Instantiation Options
% 2.31/0.97  
% 2.31/0.97  --instantiation_flag                    true
% 2.31/0.97  --inst_sos_flag                         false
% 2.31/0.97  --inst_sos_phase                        true
% 2.31/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.97  --inst_lit_sel_side                     none
% 2.31/0.97  --inst_solver_per_active                1400
% 2.31/0.97  --inst_solver_calls_frac                1.
% 2.31/0.97  --inst_passive_queue_type               priority_queues
% 2.31/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.97  --inst_passive_queues_freq              [25;2]
% 2.31/0.97  --inst_dismatching                      true
% 2.31/0.97  --inst_eager_unprocessed_to_passive     true
% 2.31/0.97  --inst_prop_sim_given                   true
% 2.31/0.97  --inst_prop_sim_new                     false
% 2.31/0.97  --inst_subs_new                         false
% 2.31/0.97  --inst_eq_res_simp                      false
% 2.31/0.97  --inst_subs_given                       false
% 2.31/0.97  --inst_orphan_elimination               true
% 2.31/0.97  --inst_learning_loop_flag               true
% 2.31/0.97  --inst_learning_start                   3000
% 2.31/0.97  --inst_learning_factor                  2
% 2.31/0.97  --inst_start_prop_sim_after_learn       3
% 2.31/0.97  --inst_sel_renew                        solver
% 2.31/0.97  --inst_lit_activity_flag                true
% 2.31/0.97  --inst_restr_to_given                   false
% 2.31/0.97  --inst_activity_threshold               500
% 2.31/0.97  --inst_out_proof                        true
% 2.31/0.97  
% 2.31/0.97  ------ Resolution Options
% 2.31/0.97  
% 2.31/0.97  --resolution_flag                       false
% 2.31/0.97  --res_lit_sel                           adaptive
% 2.31/0.97  --res_lit_sel_side                      none
% 2.31/0.97  --res_ordering                          kbo
% 2.31/0.97  --res_to_prop_solver                    active
% 2.31/0.97  --res_prop_simpl_new                    false
% 2.31/0.97  --res_prop_simpl_given                  true
% 2.31/0.97  --res_passive_queue_type                priority_queues
% 2.31/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.97  --res_passive_queues_freq               [15;5]
% 2.31/0.97  --res_forward_subs                      full
% 2.31/0.97  --res_backward_subs                     full
% 2.31/0.97  --res_forward_subs_resolution           true
% 2.31/0.97  --res_backward_subs_resolution          true
% 2.31/0.97  --res_orphan_elimination                true
% 2.31/0.97  --res_time_limit                        2.
% 2.31/0.97  --res_out_proof                         true
% 2.31/0.97  
% 2.31/0.97  ------ Superposition Options
% 2.31/0.97  
% 2.31/0.97  --superposition_flag                    true
% 2.31/0.97  --sup_passive_queue_type                priority_queues
% 2.31/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.97  --demod_completeness_check              fast
% 2.31/0.97  --demod_use_ground                      true
% 2.31/0.97  --sup_to_prop_solver                    passive
% 2.31/0.97  --sup_prop_simpl_new                    true
% 2.31/0.97  --sup_prop_simpl_given                  true
% 2.31/0.97  --sup_fun_splitting                     false
% 2.31/0.97  --sup_smt_interval                      50000
% 2.31/0.97  
% 2.31/0.97  ------ Superposition Simplification Setup
% 2.31/0.97  
% 2.31/0.97  --sup_indices_passive                   []
% 2.31/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_full_bw                           [BwDemod]
% 2.31/0.97  --sup_immed_triv                        [TrivRules]
% 2.31/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_immed_bw_main                     []
% 2.31/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.97  
% 2.31/0.97  ------ Combination Options
% 2.31/0.97  
% 2.31/0.97  --comb_res_mult                         3
% 2.31/0.97  --comb_sup_mult                         2
% 2.31/0.97  --comb_inst_mult                        10
% 2.31/0.97  
% 2.31/0.97  ------ Debug Options
% 2.31/0.97  
% 2.31/0.97  --dbg_backtrace                         false
% 2.31/0.97  --dbg_dump_prop_clauses                 false
% 2.31/0.97  --dbg_dump_prop_clauses_file            -
% 2.31/0.97  --dbg_out_stat                          false
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  ------ Proving...
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  % SZS status Theorem for theBenchmark.p
% 2.31/0.97  
% 2.31/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/0.97  
% 2.31/0.97  fof(f12,conjecture,(
% 2.31/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f13,negated_conjecture,(
% 2.31/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.31/0.97    inference(negated_conjecture,[],[f12])).
% 2.31/0.97  
% 2.31/0.97  fof(f29,plain,(
% 2.31/0.97    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.31/0.97    inference(ennf_transformation,[],[f13])).
% 2.31/0.97  
% 2.31/0.97  fof(f30,plain,(
% 2.31/0.97    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.31/0.97    inference(flattening,[],[f29])).
% 2.31/0.97  
% 2.31/0.97  fof(f31,plain,(
% 2.31/0.97    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.31/0.97    introduced(choice_axiom,[])).
% 2.31/0.97  
% 2.31/0.97  fof(f32,plain,(
% 2.31/0.97    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.31/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 2.31/0.97  
% 2.31/0.97  fof(f50,plain,(
% 2.31/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.31/0.97    inference(cnf_transformation,[],[f32])).
% 2.31/0.97  
% 2.31/0.97  fof(f9,axiom,(
% 2.31/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f25,plain,(
% 2.31/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.97    inference(ennf_transformation,[],[f9])).
% 2.31/0.97  
% 2.31/0.97  fof(f43,plain,(
% 2.31/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.97    inference(cnf_transformation,[],[f25])).
% 2.31/0.97  
% 2.31/0.97  fof(f52,plain,(
% 2.31/0.97    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.31/0.97    inference(cnf_transformation,[],[f32])).
% 2.31/0.97  
% 2.31/0.97  fof(f2,axiom,(
% 2.31/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f16,plain,(
% 2.31/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.31/0.97    inference(ennf_transformation,[],[f2])).
% 2.31/0.97  
% 2.31/0.97  fof(f34,plain,(
% 2.31/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f16])).
% 2.31/0.97  
% 2.31/0.97  fof(f3,axiom,(
% 2.31/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f35,plain,(
% 2.31/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.31/0.97    inference(cnf_transformation,[],[f3])).
% 2.31/0.97  
% 2.31/0.97  fof(f7,axiom,(
% 2.31/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f22,plain,(
% 2.31/0.97    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.31/0.97    inference(ennf_transformation,[],[f7])).
% 2.31/0.97  
% 2.31/0.97  fof(f23,plain,(
% 2.31/0.97    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.31/0.97    inference(flattening,[],[f22])).
% 2.31/0.97  
% 2.31/0.97  fof(f40,plain,(
% 2.31/0.97    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f23])).
% 2.31/0.97  
% 2.31/0.97  fof(f51,plain,(
% 2.31/0.97    v2_funct_1(sK2)),
% 2.31/0.97    inference(cnf_transformation,[],[f32])).
% 2.31/0.97  
% 2.31/0.97  fof(f48,plain,(
% 2.31/0.97    v1_funct_1(sK2)),
% 2.31/0.97    inference(cnf_transformation,[],[f32])).
% 2.31/0.97  
% 2.31/0.97  fof(f1,axiom,(
% 2.31/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f14,plain,(
% 2.31/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.31/0.97    inference(unused_predicate_definition_removal,[],[f1])).
% 2.31/0.97  
% 2.31/0.97  fof(f15,plain,(
% 2.31/0.97    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.31/0.97    inference(ennf_transformation,[],[f14])).
% 2.31/0.97  
% 2.31/0.97  fof(f33,plain,(
% 2.31/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.31/0.97    inference(cnf_transformation,[],[f15])).
% 2.31/0.97  
% 2.31/0.97  fof(f11,axiom,(
% 2.31/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f27,plain,(
% 2.31/0.97    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.31/0.97    inference(ennf_transformation,[],[f11])).
% 2.31/0.97  
% 2.31/0.97  fof(f28,plain,(
% 2.31/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.31/0.97    inference(flattening,[],[f27])).
% 2.31/0.97  
% 2.31/0.97  fof(f47,plain,(
% 2.31/0.97    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f28])).
% 2.31/0.97  
% 2.31/0.97  fof(f41,plain,(
% 2.31/0.97    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f23])).
% 2.31/0.97  
% 2.31/0.97  fof(f5,axiom,(
% 2.31/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f18,plain,(
% 2.31/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.31/0.97    inference(ennf_transformation,[],[f5])).
% 2.31/0.97  
% 2.31/0.97  fof(f19,plain,(
% 2.31/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.31/0.97    inference(flattening,[],[f18])).
% 2.31/0.97  
% 2.31/0.97  fof(f37,plain,(
% 2.31/0.97    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f19])).
% 2.31/0.97  
% 2.31/0.97  fof(f38,plain,(
% 2.31/0.97    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f19])).
% 2.31/0.97  
% 2.31/0.97  fof(f46,plain,(
% 2.31/0.97    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f28])).
% 2.31/0.97  
% 2.31/0.97  fof(f53,plain,(
% 2.31/0.97    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.31/0.97    inference(cnf_transformation,[],[f32])).
% 2.31/0.97  
% 2.31/0.97  fof(f4,axiom,(
% 2.31/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f17,plain,(
% 2.31/0.97    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.31/0.97    inference(ennf_transformation,[],[f4])).
% 2.31/0.97  
% 2.31/0.97  fof(f36,plain,(
% 2.31/0.97    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f17])).
% 2.31/0.97  
% 2.31/0.97  fof(f6,axiom,(
% 2.31/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f20,plain,(
% 2.31/0.97    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.31/0.97    inference(ennf_transformation,[],[f6])).
% 2.31/0.97  
% 2.31/0.97  fof(f21,plain,(
% 2.31/0.97    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.31/0.97    inference(flattening,[],[f20])).
% 2.31/0.97  
% 2.31/0.97  fof(f39,plain,(
% 2.31/0.97    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.31/0.97    inference(cnf_transformation,[],[f21])).
% 2.31/0.97  
% 2.31/0.97  fof(f10,axiom,(
% 2.31/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f26,plain,(
% 2.31/0.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.97    inference(ennf_transformation,[],[f10])).
% 2.31/0.97  
% 2.31/0.97  fof(f44,plain,(
% 2.31/0.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.97    inference(cnf_transformation,[],[f26])).
% 2.31/0.97  
% 2.31/0.97  fof(f8,axiom,(
% 2.31/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.31/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.97  
% 2.31/0.97  fof(f24,plain,(
% 2.31/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.97    inference(ennf_transformation,[],[f8])).
% 2.31/0.97  
% 2.31/0.97  fof(f42,plain,(
% 2.31/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.97    inference(cnf_transformation,[],[f24])).
% 2.31/0.97  
% 2.31/0.97  cnf(c_18,negated_conjecture,
% 2.31/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.31/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_495,negated_conjecture,
% 2.31/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_18]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_827,plain,
% 2.31/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_10,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_498,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.31/0.97      | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_825,plain,
% 2.31/0.97      ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
% 2.31/0.97      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1369,plain,
% 2.31/0.97      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_827,c_825]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_16,negated_conjecture,
% 2.31/0.97      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.31/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_496,negated_conjecture,
% 2.31/0.97      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_16]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1370,plain,
% 2.31/0.97      ( k2_relat_1(sK2) = sK1 ),
% 2.31/0.97      inference(light_normalisation,[status(thm)],[c_1369,c_496]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.97      | ~ v1_relat_1(X1)
% 2.31/0.97      | v1_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_504,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.31/0.97      | ~ v1_relat_1(X1_46)
% 2.31/0.97      | v1_relat_1(X0_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_819,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.31/0.97      | v1_relat_1(X1_46) != iProver_top
% 2.31/0.97      | v1_relat_1(X0_46) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1114,plain,
% 2.31/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.31/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_827,c_819]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_23,plain,
% 2.31/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_968,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.31/0.97      | v1_relat_1(X0_46)
% 2.31/0.97      | ~ v1_relat_1(k2_zfmisc_1(X1_46,X2_46)) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_504]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1045,plain,
% 2.31/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.31/0.97      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.31/0.97      | v1_relat_1(sK2) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_968]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1046,plain,
% 2.31/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.31/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_2,plain,
% 2.31/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.31/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_503,plain,
% 2.31/0.97      ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1069,plain,
% 2.31/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_503]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1070,plain,
% 2.31/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1171,plain,
% 2.31/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_1114,c_23,c_1046,c_1070]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_8,plain,
% 2.31/0.97      ( ~ v2_funct_1(X0)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_17,negated_conjecture,
% 2.31/0.97      ( v2_funct_1(sK2) ),
% 2.31/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_316,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.31/0.97      | sK2 != X0 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_317,plain,
% 2.31/0.97      ( ~ v1_funct_1(sK2)
% 2.31/0.97      | ~ v1_relat_1(sK2)
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_316]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_20,negated_conjecture,
% 2.31/0.97      ( v1_funct_1(sK2) ),
% 2.31/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_319,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_317,c_20]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_490,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_319]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_832,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1178,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1171,c_832]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1460,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.31/0.97      inference(demodulation,[status(thm)],[c_1370,c_1178]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_0,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.31/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_12,plain,
% 2.31/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.31/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_268,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
% 2.31/0.97      | ~ v1_funct_1(X2)
% 2.31/0.97      | ~ v1_relat_1(X2)
% 2.31/0.97      | X3 != X1
% 2.31/0.97      | k2_relat_1(X2) != X0 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_269,plain,
% 2.31/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.31/0.97      | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0) ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_268]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_492,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46)))
% 2.31/0.97      | ~ m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46))
% 2.31/0.97      | ~ v1_funct_1(X0_46)
% 2.31/0.97      | ~ v1_relat_1(X0_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_269]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_830,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46))) = iProver_top
% 2.31/0.97      | m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46)) != iProver_top
% 2.31/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.31/0.97      | v1_relat_1(X0_46) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1916,plain,
% 2.31/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
% 2.31/0.97      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(X0_46)) != iProver_top
% 2.31/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1460,c_830]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_7,plain,
% 2.31/0.97      ( ~ v2_funct_1(X0)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_330,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.31/0.97      | sK2 != X0 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_331,plain,
% 2.31/0.97      ( ~ v1_funct_1(sK2)
% 2.31/0.97      | ~ v1_relat_1(sK2)
% 2.31/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_330]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_46,plain,
% 2.31/0.97      ( ~ v2_funct_1(sK2)
% 2.31/0.97      | ~ v1_funct_1(sK2)
% 2.31/0.97      | ~ v1_relat_1(sK2)
% 2.31/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_333,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_331,c_20,c_17,c_46]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_489,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_333]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_833,plain,
% 2.31/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1177,plain,
% 2.31/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1171,c_833]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1940,plain,
% 2.31/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
% 2.31/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.31/0.97      inference(light_normalisation,[status(thm)],[c_1916,c_1177]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_21,plain,
% 2.31/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_5,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | v1_relat_1(k2_funct_1(X0)) ),
% 2.31/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_51,plain,
% 2.31/0.97      ( v1_funct_1(X0) != iProver_top
% 2.31/0.97      | v1_relat_1(X0) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_53,plain,
% 2.31/0.97      ( v1_funct_1(sK2) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_51]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_4,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0)
% 2.31/0.97      | v1_funct_1(k2_funct_1(X0))
% 2.31/0.97      | ~ v1_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_54,plain,
% 2.31/0.97      ( v1_funct_1(X0) != iProver_top
% 2.31/0.97      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.31/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_56,plain,
% 2.31/0.97      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.31/0.97      | v1_funct_1(sK2) != iProver_top
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_54]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_2395,plain,
% 2.31/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_1940,c_21,c_23,c_53,c_56,c_1046,c_1070]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_13,plain,
% 2.31/0.97      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.31/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_15,negated_conjecture,
% 2.31/0.97      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.31/0.97      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.31/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_223,plain,
% 2.31/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k2_funct_1(sK2) != X0
% 2.31/0.97      | k1_relat_1(X0) != sK1
% 2.31/0.97      | sK0 != X1 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_224,plain,
% 2.31/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.31/0.97      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_223]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_286,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.97      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.31/0.97      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.31/0.97      | k2_relat_1(k2_funct_1(sK2)) != X0
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.31/0.97      | sK0 != X1 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_224]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_287,plain,
% 2.31/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.31/0.97      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_286]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_491,plain,
% 2.31/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.31/0.97      | ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 2.31/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.31/0.97      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.31/0.97      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_287]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_831,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.31/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
% 2.31/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1218,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.31/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
% 2.31/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.31/0.97      inference(demodulation,[status(thm)],[c_1177,c_831]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1308,plain,
% 2.31/0.97      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.31/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_1218,c_21,c_23,c_53,c_56,c_1046,c_1070]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1312,plain,
% 2.31/0.97      ( k2_relat_1(sK2) != sK1
% 2.31/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 2.31/0.97      inference(light_normalisation,[status(thm)],[c_1308,c_1178]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1458,plain,
% 2.31/0.97      ( sK1 != sK1
% 2.31/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 2.31/0.97      inference(demodulation,[status(thm)],[c_1370,c_1312]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1465,plain,
% 2.31/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.31/0.97      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 2.31/0.97      inference(equality_resolution_simp,[status(thm)],[c_1458]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_2403,plain,
% 2.31/0.97      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_2395,c_1465]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_494,negated_conjecture,
% 2.31/0.97      ( v1_funct_1(sK2) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_20]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_828,plain,
% 2.31/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_500,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0_46)
% 2.31/0.97      | ~ v1_relat_1(X0_46)
% 2.31/0.97      | v1_relat_1(k2_funct_1(X0_46)) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_823,plain,
% 2.31/0.97      ( v1_funct_1(X0_46) != iProver_top
% 2.31/0.97      | v1_relat_1(X0_46) != iProver_top
% 2.31/0.97      | v1_relat_1(k2_funct_1(X0_46)) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_3,plain,
% 2.31/0.97      ( ~ v1_relat_1(X0)
% 2.31/0.97      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.31/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_502,plain,
% 2.31/0.97      ( ~ v1_relat_1(X0_46)
% 2.31/0.97      | k9_relat_1(X0_46,k1_relat_1(X0_46)) = k2_relat_1(X0_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_821,plain,
% 2.31/0.97      ( k9_relat_1(X0_46,k1_relat_1(X0_46)) = k2_relat_1(X0_46)
% 2.31/0.97      | v1_relat_1(X0_46) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1166,plain,
% 2.31/0.97      ( k9_relat_1(k2_funct_1(X0_46),k1_relat_1(k2_funct_1(X0_46))) = k2_relat_1(k2_funct_1(X0_46))
% 2.31/0.97      | v1_funct_1(X0_46) != iProver_top
% 2.31/0.97      | v1_relat_1(X0_46) != iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_823,c_821]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1756,plain,
% 2.31/0.97      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_828,c_1166]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1768,plain,
% 2.31/0.97      ( k9_relat_1(k2_funct_1(sK2),sK1) = k1_relat_1(sK2)
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(light_normalisation,[status(thm)],[c_1756,c_1177,c_1460]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_6,plain,
% 2.31/0.97      ( ~ v2_funct_1(X0)
% 2.31/0.97      | ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.31/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_344,plain,
% 2.31/0.97      ( ~ v1_funct_1(X0)
% 2.31/0.97      | ~ v1_relat_1(X0)
% 2.31/0.97      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.31/0.97      | sK2 != X0 ),
% 2.31/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_345,plain,
% 2.31/0.97      ( ~ v1_funct_1(sK2)
% 2.31/0.97      | ~ v1_relat_1(sK2)
% 2.31/0.97      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.31/0.97      inference(unflattening,[status(thm)],[c_344]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_349,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_345,c_20]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_488,plain,
% 2.31/0.97      ( ~ v1_relat_1(sK2)
% 2.31/0.97      | k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_349]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_834,plain,
% 2.31/0.97      ( k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46)
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1176,plain,
% 2.31/0.97      ( k9_relat_1(k2_funct_1(sK2),X0_46) = k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1171,c_834]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1769,plain,
% 2.31/0.97      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
% 2.31/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.31/0.97      inference(demodulation,[status(thm)],[c_1768,c_1176]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1817,plain,
% 2.31/0.97      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_1769,c_23,c_1046,c_1070]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_11,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.31/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_497,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.31/0.97      | k8_relset_1(X1_46,X2_46,X0_46,X3_46) = k10_relat_1(X0_46,X3_46) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_826,plain,
% 2.31/0.97      ( k8_relset_1(X0_46,X1_46,X2_46,X3_46) = k10_relat_1(X2_46,X3_46)
% 2.31/0.97      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1474,plain,
% 2.31/0.97      ( k8_relset_1(sK0,sK1,sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_827,c_826]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_9,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.97      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 2.31/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_499,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.31/0.97      | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) ),
% 2.31/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_824,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.31/0.97      | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1618,plain,
% 2.31/0.97      ( m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top
% 2.31/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1474,c_824]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1001,plain,
% 2.31/0.97      ( m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0))
% 2.31/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_499]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1002,plain,
% 2.31/0.97      ( m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top
% 2.31/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1006,plain,
% 2.31/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.31/0.97      | k8_relset_1(sK0,sK1,sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_497]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_507,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1098,plain,
% 2.31/0.97      ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_507]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_508,plain,
% 2.31/0.97      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.31/0.97      theory(equality) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1160,plain,
% 2.31/0.97      ( X0_46 != X1_46
% 2.31/0.97      | X0_46 = k8_relset_1(sK0,sK1,sK2,X2_46)
% 2.31/0.97      | k8_relset_1(sK0,sK1,sK2,X2_46) != X1_46 ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_508]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1272,plain,
% 2.31/0.97      ( X0_46 = k8_relset_1(sK0,sK1,sK2,X1_46)
% 2.31/0.97      | X0_46 != k10_relat_1(sK2,X1_46)
% 2.31/0.97      | k8_relset_1(sK0,sK1,sK2,X1_46) != k10_relat_1(sK2,X1_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_1160]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1295,plain,
% 2.31/0.97      ( k8_relset_1(sK0,sK1,sK2,X0_46) != k10_relat_1(sK2,X0_46)
% 2.31/0.97      | k10_relat_1(sK2,X0_46) = k8_relset_1(sK0,sK1,sK2,X0_46)
% 2.31/0.97      | k10_relat_1(sK2,X0_46) != k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_1272]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_506,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1296,plain,
% 2.31/0.97      ( k10_relat_1(sK2,X0_46) = k10_relat_1(sK2,X0_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_506]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_510,plain,
% 2.31/0.97      ( ~ m1_subset_1(X0_46,X0_47)
% 2.31/0.97      | m1_subset_1(X1_46,X1_47)
% 2.31/0.97      | X1_47 != X0_47
% 2.31/0.97      | X1_46 != X0_46 ),
% 2.31/0.97      theory(equality) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1017,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,X0_47)
% 2.31/0.97      | ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X1_46),k1_zfmisc_1(sK0))
% 2.31/0.97      | X0_47 != k1_zfmisc_1(sK0)
% 2.31/0.97      | X0_46 != k8_relset_1(sK0,sK1,sK2,X1_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_510]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1097,plain,
% 2.31/0.97      ( m1_subset_1(X0_46,k1_zfmisc_1(sK0))
% 2.31/0.97      | ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X1_46),k1_zfmisc_1(sK0))
% 2.31/0.97      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
% 2.31/0.97      | X0_46 != k8_relset_1(sK0,sK1,sK2,X1_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_1017]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1580,plain,
% 2.31/0.97      ( ~ m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0))
% 2.31/0.97      | m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0))
% 2.31/0.97      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
% 2.31/0.97      | k10_relat_1(sK2,X0_46) != k8_relset_1(sK0,sK1,sK2,X0_46) ),
% 2.31/0.97      inference(instantiation,[status(thm)],[c_1097]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1581,plain,
% 2.31/0.97      ( k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
% 2.31/0.97      | k10_relat_1(sK2,X0_46) != k8_relset_1(sK0,sK1,sK2,X0_46)
% 2.31/0.97      | m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0_46),k1_zfmisc_1(sK0)) != iProver_top
% 2.31/0.97      | m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.31/0.97      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1623,plain,
% 2.31/0.97      ( m1_subset_1(k10_relat_1(sK2,X0_46),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.31/0.97      inference(global_propositional_subsumption,
% 2.31/0.97                [status(thm)],
% 2.31/0.97                [c_1618,c_18,c_23,c_1002,c_1006,c_1098,c_1295,c_1296,
% 2.31/0.97                 c_1581]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(c_1821,plain,
% 2.31/0.97      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.31/0.97      inference(superposition,[status(thm)],[c_1817,c_1623]) ).
% 2.31/0.97  
% 2.31/0.97  cnf(contradiction,plain,
% 2.31/0.97      ( $false ),
% 2.31/0.97      inference(minisat,[status(thm)],[c_2403,c_1821]) ).
% 2.31/0.97  
% 2.31/0.97  
% 2.31/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/0.97  
% 2.31/0.97  ------                               Statistics
% 2.31/0.97  
% 2.31/0.97  ------ General
% 2.31/0.97  
% 2.31/0.97  abstr_ref_over_cycles:                  0
% 2.31/0.97  abstr_ref_under_cycles:                 0
% 2.31/0.97  gc_basic_clause_elim:                   0
% 2.31/0.97  forced_gc_time:                         0
% 2.31/0.97  parsing_time:                           0.011
% 2.31/0.97  unif_index_cands_time:                  0.
% 2.31/0.97  unif_index_add_time:                    0.
% 2.31/0.97  orderings_time:                         0.
% 2.31/0.97  out_proof_time:                         0.013
% 2.31/0.97  total_time:                             0.122
% 2.31/0.97  num_of_symbols:                         51
% 2.31/0.97  num_of_terms:                           1955
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing
% 2.31/0.98  
% 2.31/0.98  num_of_splits:                          0
% 2.31/0.98  num_of_split_atoms:                     0
% 2.31/0.98  num_of_reused_defs:                     0
% 2.31/0.98  num_eq_ax_congr_red:                    17
% 2.31/0.98  num_of_sem_filtered_clauses:            1
% 2.31/0.98  num_of_subtypes:                        2
% 2.31/0.98  monotx_restored_types:                  0
% 2.31/0.98  sat_num_of_epr_types:                   0
% 2.31/0.98  sat_num_of_non_cyclic_types:            0
% 2.31/0.98  sat_guarded_non_collapsed_types:        0
% 2.31/0.98  num_pure_diseq_elim:                    0
% 2.31/0.98  simp_replaced_by:                       0
% 2.31/0.98  res_preprocessed:                       100
% 2.31/0.98  prep_upred:                             0
% 2.31/0.98  prep_unflattend:                        9
% 2.31/0.98  smt_new_axioms:                         0
% 2.31/0.98  pred_elim_cands:                        3
% 2.31/0.98  pred_elim:                              3
% 2.31/0.98  pred_elim_cl:                           3
% 2.31/0.98  pred_elim_cycles:                       5
% 2.31/0.98  merged_defs:                            0
% 2.31/0.98  merged_defs_ncl:                        0
% 2.31/0.98  bin_hyper_res:                          0
% 2.31/0.98  prep_cycles:                            4
% 2.31/0.98  pred_elim_time:                         0.003
% 2.31/0.98  splitting_time:                         0.
% 2.31/0.98  sem_filter_time:                        0.
% 2.31/0.98  monotx_time:                            0.
% 2.31/0.98  subtype_inf_time:                       0.001
% 2.31/0.98  
% 2.31/0.98  ------ Problem properties
% 2.31/0.98  
% 2.31/0.98  clauses:                                17
% 2.31/0.98  conjectures:                            3
% 2.31/0.98  epr:                                    1
% 2.31/0.98  horn:                                   17
% 2.31/0.98  ground:                                 7
% 2.31/0.98  unary:                                  4
% 2.31/0.98  binary:                                 7
% 2.31/0.98  lits:                                   40
% 2.31/0.98  lits_eq:                                10
% 2.31/0.98  fd_pure:                                0
% 2.31/0.98  fd_pseudo:                              0
% 2.31/0.98  fd_cond:                                0
% 2.31/0.98  fd_pseudo_cond:                         0
% 2.31/0.98  ac_symbols:                             0
% 2.31/0.98  
% 2.31/0.98  ------ Propositional Solver
% 2.31/0.98  
% 2.31/0.98  prop_solver_calls:                      31
% 2.31/0.98  prop_fast_solver_calls:                 625
% 2.31/0.98  smt_solver_calls:                       0
% 2.31/0.98  smt_fast_solver_calls:                  0
% 2.31/0.98  prop_num_of_clauses:                    759
% 2.31/0.98  prop_preprocess_simplified:             3313
% 2.31/0.98  prop_fo_subsumed:                       15
% 2.31/0.98  prop_solver_time:                       0.
% 2.31/0.98  smt_solver_time:                        0.
% 2.31/0.98  smt_fast_solver_time:                   0.
% 2.31/0.98  prop_fast_solver_time:                  0.
% 2.31/0.98  prop_unsat_core_time:                   0.
% 2.31/0.98  
% 2.31/0.98  ------ QBF
% 2.31/0.98  
% 2.31/0.98  qbf_q_res:                              0
% 2.31/0.98  qbf_num_tautologies:                    0
% 2.31/0.98  qbf_prep_cycles:                        0
% 2.31/0.98  
% 2.31/0.98  ------ BMC1
% 2.31/0.98  
% 2.31/0.98  bmc1_current_bound:                     -1
% 2.31/0.98  bmc1_last_solved_bound:                 -1
% 2.31/0.98  bmc1_unsat_core_size:                   -1
% 2.31/0.98  bmc1_unsat_core_parents_size:           -1
% 2.31/0.98  bmc1_merge_next_fun:                    0
% 2.31/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.31/0.98  
% 2.31/0.98  ------ Instantiation
% 2.31/0.98  
% 2.31/0.98  inst_num_of_clauses:                    281
% 2.31/0.98  inst_num_in_passive:                    76
% 2.31/0.98  inst_num_in_active:                     198
% 2.31/0.98  inst_num_in_unprocessed:                8
% 2.31/0.98  inst_num_of_loops:                      220
% 2.31/0.98  inst_num_of_learning_restarts:          0
% 2.31/0.98  inst_num_moves_active_passive:          15
% 2.31/0.98  inst_lit_activity:                      0
% 2.31/0.98  inst_lit_activity_moves:                0
% 2.31/0.98  inst_num_tautologies:                   0
% 2.31/0.98  inst_num_prop_implied:                  0
% 2.31/0.98  inst_num_existing_simplified:           0
% 2.31/0.98  inst_num_eq_res_simplified:             0
% 2.31/0.98  inst_num_child_elim:                    0
% 2.31/0.98  inst_num_of_dismatching_blockings:      59
% 2.31/0.98  inst_num_of_non_proper_insts:           342
% 2.31/0.98  inst_num_of_duplicates:                 0
% 2.31/0.98  inst_inst_num_from_inst_to_res:         0
% 2.31/0.98  inst_dismatching_checking_time:         0.
% 2.31/0.98  
% 2.31/0.98  ------ Resolution
% 2.31/0.98  
% 2.31/0.98  res_num_of_clauses:                     0
% 2.31/0.98  res_num_in_passive:                     0
% 2.31/0.98  res_num_in_active:                      0
% 2.31/0.98  res_num_of_loops:                       104
% 2.31/0.98  res_forward_subset_subsumed:            50
% 2.31/0.98  res_backward_subset_subsumed:           4
% 2.31/0.98  res_forward_subsumed:                   0
% 2.31/0.98  res_backward_subsumed:                  0
% 2.31/0.98  res_forward_subsumption_resolution:     0
% 2.31/0.98  res_backward_subsumption_resolution:    0
% 2.31/0.98  res_clause_to_clause_subsumption:       99
% 2.31/0.98  res_orphan_elimination:                 0
% 2.31/0.98  res_tautology_del:                      85
% 2.31/0.98  res_num_eq_res_simplified:              0
% 2.31/0.98  res_num_sel_changes:                    0
% 2.31/0.98  res_moves_from_active_to_pass:          0
% 2.31/0.98  
% 2.31/0.98  ------ Superposition
% 2.31/0.98  
% 2.31/0.98  sup_time_total:                         0.
% 2.31/0.98  sup_time_generating:                    0.
% 2.31/0.98  sup_time_sim_full:                      0.
% 2.31/0.98  sup_time_sim_immed:                     0.
% 2.31/0.98  
% 2.31/0.98  sup_num_of_clauses:                     47
% 2.31/0.98  sup_num_in_active:                      36
% 2.31/0.98  sup_num_in_passive:                     11
% 2.31/0.98  sup_num_of_loops:                       42
% 2.31/0.98  sup_fw_superposition:                   19
% 2.31/0.98  sup_bw_superposition:                   21
% 2.31/0.98  sup_immediate_simplified:               6
% 2.31/0.98  sup_given_eliminated:                   0
% 2.31/0.98  comparisons_done:                       0
% 2.31/0.98  comparisons_avoided:                    0
% 2.31/0.98  
% 2.31/0.98  ------ Simplifications
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  sim_fw_subset_subsumed:                 0
% 2.31/0.98  sim_bw_subset_subsumed:                 3
% 2.31/0.98  sim_fw_subsumed:                        0
% 2.31/0.98  sim_bw_subsumed:                        0
% 2.31/0.98  sim_fw_subsumption_res:                 0
% 2.31/0.98  sim_bw_subsumption_res:                 0
% 2.31/0.98  sim_tautology_del:                      1
% 2.31/0.98  sim_eq_tautology_del:                   0
% 2.31/0.98  sim_eq_res_simp:                        1
% 2.31/0.98  sim_fw_demodulated:                     1
% 2.31/0.98  sim_bw_demodulated:                     4
% 2.31/0.98  sim_light_normalised:                   8
% 2.31/0.98  sim_joinable_taut:                      0
% 2.31/0.98  sim_joinable_simp:                      0
% 2.31/0.98  sim_ac_normalised:                      0
% 2.31/0.98  sim_smt_subsumption:                    0
% 2.31/0.98  
%------------------------------------------------------------------------------
