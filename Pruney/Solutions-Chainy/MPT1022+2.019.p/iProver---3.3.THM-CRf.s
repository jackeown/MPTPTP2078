%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:39 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  214 (1242 expanded)
%              Number of clauses        :  145 ( 428 expanded)
%              Number of leaves         :   20 ( 238 expanded)
%              Depth                    :   20
%              Number of atoms          :  687 (6294 expanded)
%              Number of equality atoms :  304 (1763 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
        | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f43])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_700,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_702,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1158,plain,
    ( k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1943,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1158])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_782,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_2109,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_27,c_26,c_25,c_24,c_782])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_706,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1154,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2439,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_1154])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2982,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2439,c_28,c_29,c_30,c_31])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_410,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_411,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_427,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_411,c_8])).

cnf(c_693,plain,
    ( ~ v3_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_relat_1(X0_52) = X1_53 ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_1166,plain,
    ( k2_relat_1(X0_52) = X0_53
    | v3_funct_2(X0_52,X1_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2996,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1166])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_91,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_93,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_769,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_771,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(k2_funct_2(X0_53,X0_52))
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1551,plain,
    ( m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(k2_funct_2(X0_53,X0_52)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_1553,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_719,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1483,plain,
    ( X0_52 != X1_52
    | X0_52 = k2_funct_2(X0_53,X2_52)
    | k2_funct_2(X0_53,X2_52) != X1_52 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1543,plain,
    ( X0_52 = k2_funct_2(X0_53,X1_52)
    | X0_52 != k2_funct_1(X1_52)
    | k2_funct_2(X0_53,X1_52) != k2_funct_1(X1_52) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1679,plain,
    ( k2_funct_2(X0_53,X0_52) != k2_funct_1(X0_52)
    | k2_funct_1(X0_52) = k2_funct_2(X0_53,X0_52)
    | k2_funct_1(X0_52) != k2_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1681,plain,
    ( k2_funct_2(sK0,sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_716,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1680,plain,
    ( k2_funct_1(X0_52) = k2_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1682,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_703,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1157,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1864,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1157])).

cnf(c_778,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_780,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_2018,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_28,c_29,c_30,c_31,c_780])).

cnf(c_2112,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2109,c_2018])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_705,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1155,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1951,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1155])).

cnf(c_772,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_774,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_2115,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1951,c_28,c_29,c_30,c_31,c_774])).

cnf(c_2119,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2115,c_2109])).

cnf(c_721,plain,
    ( ~ v1_relat_1(X0_52)
    | v1_relat_1(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1831,plain,
    ( ~ v1_relat_1(X0_52)
    | v1_relat_1(k2_funct_1(X1_52))
    | k2_funct_1(X1_52) != X0_52 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2266,plain,
    ( ~ v1_relat_1(k2_funct_2(X0_53,X0_52))
    | v1_relat_1(k2_funct_1(X0_52))
    | k2_funct_1(X0_52) != k2_funct_2(X0_53,X0_52) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2267,plain,
    ( k2_funct_1(X0_52) != k2_funct_2(X0_53,X0_52)
    | v1_relat_1(k2_funct_2(X0_53,X0_52)) != iProver_top
    | v1_relat_1(k2_funct_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2266])).

cnf(c_2269,plain,
    ( k2_funct_1(sK2) != k2_funct_2(sK0,sK2)
    | v1_relat_1(k2_funct_2(sK0,sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_3621,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2996,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_93,c_771,c_782,c_1553,c_1681,c_1682,c_2112,c_2119,c_2269])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_4])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(X0_52)
    | k7_relat_1(X0_52,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_1163,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_713,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_750,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_788,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_1370,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_2681,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k7_relat_1(X0_52,X0_53) = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1163,c_750,c_788,c_1370])).

cnf(c_2682,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2681])).

cnf(c_2987,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2982,c_2682])).

cnf(c_1146,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2995,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1146])).

cnf(c_3284,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_93,c_771,c_782,c_1553,c_1681,c_1682,c_2269])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_712,plain,
    ( ~ v1_relat_1(X0_52)
    | k2_relat_1(k7_relat_1(X0_52,X0_53)) = k9_relat_1(X0_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1148,plain,
    ( k2_relat_1(k7_relat_1(X0_52,X0_53)) = k9_relat_1(X0_52,X0_53)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_3289,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_53)) = k9_relat_1(k2_funct_1(sK2),X0_53) ),
    inference(superposition,[status(thm)],[c_3284,c_1148])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_707,plain,
    ( ~ v3_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v2_funct_1(X0_52)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1153,plain,
    ( v3_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v2_funct_1(X0_52) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_1856,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1153])).

cnf(c_766,plain,
    ( v3_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v2_funct_1(X0_52) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_768,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_2008,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1856,c_28,c_30,c_31,c_768])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_710,plain,
    ( ~ v2_funct_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k9_relat_1(k2_funct_1(X0_52),X0_53) = k10_relat_1(X0_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1150,plain,
    ( k9_relat_1(k2_funct_1(X0_52),X0_53) = k10_relat_1(X0_52,X0_53)
    | v2_funct_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2013,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_1150])).

cnf(c_1372,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2232,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_28,c_31,c_93,c_1372])).

cnf(c_3294,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_53)) = k10_relat_1(sK2,X0_53) ),
    inference(light_normalisation,[status(thm)],[c_3289,c_2232])).

cnf(c_3493,plain,
    ( k10_relat_1(sK2,sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2987,c_3294])).

cnf(c_2753,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1166])).

cnf(c_92,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_798,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_2784,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2753,c_27,c_25,c_24,c_92,c_798,c_1371])).

cnf(c_1458,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1146])).

cnf(c_1603,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1458,c_31,c_93,c_1372])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_711,plain,
    ( ~ v1_relat_1(X0_52)
    | k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1149,plain,
    ( k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_1609,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1603,c_1149])).

cnf(c_2787,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2784,c_1609])).

cnf(c_3504,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3493,c_2787])).

cnf(c_3624,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3621,c_3504])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k7_relset_1(X0_53,X1_53,X0_52,X2_53) = k9_relat_1(X0_52,X2_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1151,plain,
    ( k7_relset_1(X0_53,X1_53,X0_52,X2_53) = k9_relat_1(X0_52,X2_53)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_1493,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0_53) = k9_relat_1(sK2,X0_53) ),
    inference(superposition,[status(thm)],[c_1159,c_1151])).

cnf(c_22,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_701,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1539,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1493,c_701])).

cnf(c_1540,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1539,c_1493])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1152,plain,
    ( k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1536,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(superposition,[status(thm)],[c_1159,c_1152])).

cnf(c_1665,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1540,c_1536])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_339,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | k1_relat_1(X0) != sK0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_340,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k9_relat_1(X0,sK1)) = sK1
    | k1_relat_1(X0) != sK0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_694,plain,
    ( ~ v2_funct_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k10_relat_1(X0_52,k9_relat_1(X0_52,sK1)) = sK1
    | k1_relat_1(X0_52) != sK0 ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_795,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_321,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | k2_relat_1(X0) != sK0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_322,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,sK1)) = sK1
    | k2_relat_1(X0) != sK0 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_695,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k9_relat_1(X0_52,k10_relat_1(X0_52,sK1)) = sK1
    | k2_relat_1(X0_52) != sK0 ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_792,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_767,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3624,c_1665,c_1371,c_798,c_795,c_792,c_767,c_92,c_24,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.64/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/1.01  
% 2.64/1.01  ------  iProver source info
% 2.64/1.01  
% 2.64/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.64/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/1.01  git: non_committed_changes: false
% 2.64/1.01  git: last_make_outside_of_git: false
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     num_symb
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       true
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  ------ Parsing...
% 2.64/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/1.01  ------ Proving...
% 2.64/1.01  ------ Problem Properties 
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  clauses                                 22
% 2.64/1.01  conjectures                             5
% 2.64/1.01  EPR                                     3
% 2.64/1.01  Horn                                    22
% 2.64/1.01  unary                                   5
% 2.64/1.01  binary                                  5
% 2.64/1.01  lits                                    68
% 2.64/1.01  lits eq                                 14
% 2.64/1.01  fd_pure                                 0
% 2.64/1.01  fd_pseudo                               0
% 2.64/1.01  fd_cond                                 0
% 2.64/1.01  fd_pseudo_cond                          1
% 2.64/1.01  AC symbols                              0
% 2.64/1.01  
% 2.64/1.01  ------ Schedule dynamic 5 is on 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  Current options:
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     none
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       false
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ Proving...
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS status Theorem for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  fof(f16,conjecture,(
% 2.64/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f17,negated_conjecture,(
% 2.64/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 2.64/1.01    inference(negated_conjecture,[],[f16])).
% 2.64/1.01  
% 2.64/1.01  fof(f40,plain,(
% 2.64/1.01    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 2.64/1.01    inference(ennf_transformation,[],[f17])).
% 2.64/1.01  
% 2.64/1.01  fof(f41,plain,(
% 2.64/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 2.64/1.01    inference(flattening,[],[f40])).
% 2.64/1.01  
% 2.64/1.01  fof(f43,plain,(
% 2.64/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f44,plain,(
% 2.64/1.01    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 2.64/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f43])).
% 2.64/1.01  
% 2.64/1.01  fof(f70,plain,(
% 2.64/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f15,axiom,(
% 2.64/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f38,plain,(
% 2.64/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f15])).
% 2.64/1.01  
% 2.64/1.01  fof(f39,plain,(
% 2.64/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.64/1.01    inference(flattening,[],[f38])).
% 2.64/1.01  
% 2.64/1.01  fof(f66,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f39])).
% 2.64/1.01  
% 2.64/1.01  fof(f67,plain,(
% 2.64/1.01    v1_funct_1(sK2)),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f68,plain,(
% 2.64/1.01    v1_funct_2(sK2,sK0,sK0)),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f69,plain,(
% 2.64/1.01    v3_funct_2(sK2,sK0,sK0)),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f14,axiom,(
% 2.64/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f36,plain,(
% 2.64/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f14])).
% 2.64/1.01  
% 2.64/1.01  fof(f37,plain,(
% 2.64/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.64/1.01    inference(flattening,[],[f36])).
% 2.64/1.01  
% 2.64/1.01  fof(f65,plain,(
% 2.64/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f37])).
% 2.64/1.01  
% 2.64/1.01  fof(f12,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f32,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f12])).
% 2.64/1.01  
% 2.64/1.01  fof(f33,plain,(
% 2.64/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(flattening,[],[f32])).
% 2.64/1.01  
% 2.64/1.01  fof(f59,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f33])).
% 2.64/1.01  
% 2.64/1.01  fof(f13,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f34,plain,(
% 2.64/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f13])).
% 2.64/1.01  
% 2.64/1.01  fof(f35,plain,(
% 2.64/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f34])).
% 2.64/1.01  
% 2.64/1.01  fof(f42,plain,(
% 2.64/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(nnf_transformation,[],[f35])).
% 2.64/1.01  
% 2.64/1.01  fof(f60,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f42])).
% 2.64/1.01  
% 2.64/1.01  fof(f9,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f29,plain,(
% 2.64/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f9])).
% 2.64/1.01  
% 2.64/1.01  fof(f54,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f29])).
% 2.64/1.01  
% 2.64/1.01  fof(f2,axiom,(
% 2.64/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f46,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f2])).
% 2.64/1.01  
% 2.64/1.01  fof(f1,axiom,(
% 2.64/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f18,plain,(
% 2.64/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(ennf_transformation,[],[f1])).
% 2.64/1.01  
% 2.64/1.01  fof(f45,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f18])).
% 2.64/1.01  
% 2.64/1.01  fof(f62,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f37])).
% 2.64/1.01  
% 2.64/1.01  fof(f64,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f37])).
% 2.64/1.01  
% 2.64/1.01  fof(f53,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f29])).
% 2.64/1.01  
% 2.64/1.01  fof(f5,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f21,plain,(
% 2.64/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f5])).
% 2.64/1.01  
% 2.64/1.01  fof(f22,plain,(
% 2.64/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f21])).
% 2.64/1.01  
% 2.64/1.01  fof(f49,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f3,axiom,(
% 2.64/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f19,plain,(
% 2.64/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(ennf_transformation,[],[f3])).
% 2.64/1.01  
% 2.64/1.01  fof(f47,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f58,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f33])).
% 2.64/1.01  
% 2.64/1.01  fof(f7,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f25,plain,(
% 2.64/1.01    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f7])).
% 2.64/1.01  
% 2.64/1.01  fof(f26,plain,(
% 2.64/1.01    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f25])).
% 2.64/1.01  
% 2.64/1.01  fof(f51,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f26])).
% 2.64/1.01  
% 2.64/1.01  fof(f4,axiom,(
% 2.64/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f20,plain,(
% 2.64/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(ennf_transformation,[],[f4])).
% 2.64/1.01  
% 2.64/1.01  fof(f48,plain,(
% 2.64/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f20])).
% 2.64/1.01  
% 2.64/1.01  fof(f10,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f30,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f55,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f30])).
% 2.64/1.01  
% 2.64/1.01  fof(f72,plain,(
% 2.64/1.01    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f11,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f31,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f11])).
% 2.64/1.01  
% 2.64/1.01  fof(f56,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f31])).
% 2.64/1.01  
% 2.64/1.01  fof(f8,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f27,plain,(
% 2.64/1.01    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f8])).
% 2.64/1.01  
% 2.64/1.01  fof(f28,plain,(
% 2.64/1.01    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f27])).
% 2.64/1.01  
% 2.64/1.01  fof(f52,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f28])).
% 2.64/1.01  
% 2.64/1.01  fof(f71,plain,(
% 2.64/1.01    r1_tarski(sK1,sK0)),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f6,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f23,plain,(
% 2.64/1.01    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f6])).
% 2.64/1.01  
% 2.64/1.01  fof(f24,plain,(
% 2.64/1.01    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f23])).
% 2.64/1.01  
% 2.64/1.01  fof(f50,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f24])).
% 2.64/1.01  
% 2.64/1.01  cnf(c_24,negated_conjecture,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.64/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_700,negated_conjecture,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1159,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_21,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_702,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 2.64/1.01      | ~ v1_funct_1(X0_52)
% 2.64/1.01      | k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1158,plain,
% 2.64/1.01      ( k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52)
% 2.64/1.01      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1943,plain,
% 2.64/1.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 2.64/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1158]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_27,negated_conjecture,
% 2.64/1.01      ( v1_funct_1(sK2) ),
% 2.64/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_26,negated_conjecture,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_25,negated_conjecture,
% 2.64/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_782,plain,
% 2.64/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 2.64/1.01      | ~ v3_funct_2(sK2,sK0,sK0)
% 2.64/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_702]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2109,plain,
% 2.64/1.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1943,c_27,c_26,c_25,c_24,c_782]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_17,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.64/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_706,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 2.64/1.01      | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 2.64/1.01      | ~ v1_funct_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1154,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2439,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2109,c_1154]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_28,plain,
% 2.64/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_29,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_30,plain,
% 2.64/1.01      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_31,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2982,plain,
% 2.64/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2439,c_28,c_29,c_30,c_31]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_12,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.64/1.01      | v2_funct_2(X0,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_16,plain,
% 2.64/1.01      ( ~ v2_funct_2(X0,X1)
% 2.64/1.01      | ~ v5_relat_1(X0,X1)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k2_relat_1(X0) = X1 ),
% 2.64/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_410,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ v5_relat_1(X3,X4)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X3)
% 2.64/1.01      | X3 != X0
% 2.64/1.01      | X4 != X2
% 2.64/1.01      | k2_relat_1(X3) = X4 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_411,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ v5_relat_1(X0,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k2_relat_1(X0) = X2 ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_410]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_8,plain,
% 2.64/1.01      ( v5_relat_1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.64/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_427,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k2_relat_1(X0) = X2 ),
% 2.64/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_411,c_8]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_693,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0_52,X0_53,X1_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | ~ v1_funct_1(X0_52)
% 2.64/1.01      | ~ v1_relat_1(X0_52)
% 2.64/1.01      | k2_relat_1(X0_52) = X1_53 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_427]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1166,plain,
% 2.64/1.01      ( k2_relat_1(X0_52) = X0_53
% 2.64/1.01      | v3_funct_2(X0_52,X1_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2996,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 2.64/1.01      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2982,c_1166]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_91,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_93,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_91]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_769,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_771,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_769]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_0,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.64/1.01      | ~ v1_relat_1(X1)
% 2.64/1.01      | v1_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_714,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.64/1.01      | ~ v1_relat_1(X1_52)
% 2.64/1.01      | v1_relat_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1369,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | v1_relat_1(X0_52)
% 2.64/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_714]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1550,plain,
% 2.64/1.01      ( ~ m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.64/1.01      | v1_relat_1(k2_funct_2(X0_53,X0_52))
% 2.64/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1551,plain,
% 2.64/1.01      ( m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_2(X0_53,X0_52)) = iProver_top
% 2.64/1.01      | v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1553,plain,
% 2.64/1.01      ( m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_2(sK0,sK2)) = iProver_top
% 2.64/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1551]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_719,plain,
% 2.64/1.01      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 2.64/1.01      theory(equality) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1483,plain,
% 2.64/1.01      ( X0_52 != X1_52
% 2.64/1.01      | X0_52 = k2_funct_2(X0_53,X2_52)
% 2.64/1.01      | k2_funct_2(X0_53,X2_52) != X1_52 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_719]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1543,plain,
% 2.64/1.01      ( X0_52 = k2_funct_2(X0_53,X1_52)
% 2.64/1.01      | X0_52 != k2_funct_1(X1_52)
% 2.64/1.01      | k2_funct_2(X0_53,X1_52) != k2_funct_1(X1_52) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1483]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1679,plain,
% 2.64/1.01      ( k2_funct_2(X0_53,X0_52) != k2_funct_1(X0_52)
% 2.64/1.01      | k2_funct_1(X0_52) = k2_funct_2(X0_53,X0_52)
% 2.64/1.01      | k2_funct_1(X0_52) != k2_funct_1(X0_52) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1681,plain,
% 2.64/1.01      ( k2_funct_2(sK0,sK2) != k2_funct_1(sK2)
% 2.64/1.01      | k2_funct_1(sK2) = k2_funct_2(sK0,sK2)
% 2.64/1.01      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1679]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_716,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1680,plain,
% 2.64/1.01      ( k2_funct_1(X0_52) = k2_funct_1(X0_52) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_716]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1682,plain,
% 2.64/1.01      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1680]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_20,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_703,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 2.64/1.01      | ~ v1_funct_1(X0_52)
% 2.64/1.01      | v1_funct_1(k2_funct_2(X0_53,X0_52)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1157,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1864,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1157]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_778,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_780,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_778]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2018,plain,
% 2.64/1.01      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1864,c_28,c_29,c_30,c_31,c_780]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2112,plain,
% 2.64/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2109,c_2018]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_18,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.64/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.64/1.01      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_705,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 2.64/1.01      | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 2.64/1.01      | ~ v1_funct_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1155,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1951,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1155]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_772,plain,
% 2.64/1.01      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 2.64/1.01      | v3_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_774,plain,
% 2.64/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_772]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2115,plain,
% 2.64/1.01      ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1951,c_28,c_29,c_30,c_31,c_774]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2119,plain,
% 2.64/1.01      ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2115,c_2109]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_721,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0_52) | v1_relat_1(X1_52) | X1_52 != X0_52 ),
% 2.64/1.01      theory(equality) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1831,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0_52)
% 2.64/1.01      | v1_relat_1(k2_funct_1(X1_52))
% 2.64/1.01      | k2_funct_1(X1_52) != X0_52 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_721]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2266,plain,
% 2.64/1.01      ( ~ v1_relat_1(k2_funct_2(X0_53,X0_52))
% 2.64/1.01      | v1_relat_1(k2_funct_1(X0_52))
% 2.64/1.01      | k2_funct_1(X0_52) != k2_funct_2(X0_53,X0_52) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1831]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2267,plain,
% 2.64/1.01      ( k2_funct_1(X0_52) != k2_funct_2(X0_53,X0_52)
% 2.64/1.01      | v1_relat_1(k2_funct_2(X0_53,X0_52)) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(X0_52)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_2266]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2269,plain,
% 2.64/1.01      ( k2_funct_1(sK2) != k2_funct_2(sK0,sK2)
% 2.64/1.01      | v1_relat_1(k2_funct_2(sK0,sK2)) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_2267]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3621,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2996,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_93,
% 2.64/1.01                 c_771,c_782,c_1553,c_1681,c_1682,c_2112,c_2119,c_2269]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_9,plain,
% 2.64/1.01      ( v4_relat_1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.64/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4,plain,
% 2.64/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.64/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_303,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.64/1.01      inference(resolution,[status(thm)],[c_9,c_4]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_696,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | ~ v1_relat_1(X0_52)
% 2.64/1.01      | k7_relat_1(X0_52,X0_53) = X0_52 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_303]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1163,plain,
% 2.64/1.01      ( k7_relat_1(X0_52,X0_53) = X0_52
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_713,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_750,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_788,plain,
% 2.64/1.01      ( k7_relat_1(X0_52,X0_53) = X0_52
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1370,plain,
% 2.64/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) = iProver_top
% 2.64/1.01      | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2681,plain,
% 2.64/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | k7_relat_1(X0_52,X0_53) = X0_52 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1163,c_750,c_788,c_1370]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2682,plain,
% 2.64/1.01      ( k7_relat_1(X0_52,X0_53) = X0_52
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.64/1.01      inference(renaming,[status(thm)],[c_2681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2987,plain,
% 2.64/1.01      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2982,c_2682]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1146,plain,
% 2.64/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 2.64/1.01      | v1_relat_1(X1_52) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2995,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2982,c_1146]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3284,plain,
% 2.64/1.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2995,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_93,
% 2.64/1.01                 c_771,c_782,c_1553,c_1681,c_1682,c_2269]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0)
% 2.64/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.64/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_712,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0_52)
% 2.64/1.01      | k2_relat_1(k7_relat_1(X0_52,X0_53)) = k9_relat_1(X0_52,X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1148,plain,
% 2.64/1.01      ( k2_relat_1(k7_relat_1(X0_52,X0_53)) = k9_relat_1(X0_52,X0_53)
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3289,plain,
% 2.64/1.01      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_53)) = k9_relat_1(k2_funct_1(sK2),X0_53) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_3284,c_1148]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_13,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_707,plain,
% 2.64/1.01      ( ~ v3_funct_2(X0_52,X0_53,X1_53)
% 2.64/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | v2_funct_1(X0_52)
% 2.64/1.01      | ~ v1_funct_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1153,plain,
% 2.64/1.01      ( v3_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | v2_funct_1(X0_52) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1856,plain,
% 2.64/1.01      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v2_funct_1(sK2) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1153]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_766,plain,
% 2.64/1.01      ( v3_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.64/1.01      | v2_funct_1(X0_52) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_768,plain,
% 2.64/1.01      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v2_funct_1(sK2) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_766]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2008,plain,
% 2.64/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1856,c_28,c_30,c_31,c_768]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_6,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.64/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_710,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0_52)
% 2.64/1.01      | ~ v1_funct_1(X0_52)
% 2.64/1.01      | ~ v1_relat_1(X0_52)
% 2.64/1.01      | k9_relat_1(k2_funct_1(X0_52),X0_53) = k10_relat_1(X0_52,X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1150,plain,
% 2.64/1.01      ( k9_relat_1(k2_funct_1(X0_52),X0_53) = k10_relat_1(X0_52,X0_53)
% 2.64/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2013,plain,
% 2.64/1.01      ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53)
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2008,c_1150]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1372,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2232,plain,
% 2.64/1.01      ( k9_relat_1(k2_funct_1(sK2),X0_53) = k10_relat_1(sK2,X0_53) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2013,c_28,c_31,c_93,c_1372]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3294,plain,
% 2.64/1.01      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_53)) = k10_relat_1(sK2,X0_53) ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_3289,c_2232]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3493,plain,
% 2.64/1.01      ( k10_relat_1(sK2,sK0) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2987,c_3294]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2753,plain,
% 2.64/1.01      ( k2_relat_1(sK2) = sK0
% 2.64/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1166]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_92,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_798,plain,
% 2.64/1.01      ( ~ v3_funct_2(sK2,sK0,sK0)
% 2.64/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k2_relat_1(sK2) = sK0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_693]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1371,plain,
% 2.64/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.64/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.64/1.01      | v1_relat_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2784,plain,
% 2.64/1.01      ( k2_relat_1(sK2) = sK0 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2753,c_27,c_25,c_24,c_92,c_798,c_1371]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1458,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1146]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1603,plain,
% 2.64/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1458,c_31,c_93,c_1372]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0)
% 2.64/1.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_711,plain,
% 2.64/1.01      ( ~ v1_relat_1(X0_52)
% 2.64/1.01      | k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1149,plain,
% 2.64/1.01      ( k10_relat_1(X0_52,k2_relat_1(X0_52)) = k1_relat_1(X0_52)
% 2.64/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1609,plain,
% 2.64/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1603,c_1149]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2787,plain,
% 2.64/1.01      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2784,c_1609]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3504,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_3493,c_2787]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3624,plain,
% 2.64/1.01      ( k1_relat_1(sK2) = sK0 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_3621,c_3504]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_10,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.64/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_709,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | k7_relset_1(X0_53,X1_53,X0_52,X2_53) = k9_relat_1(X0_52,X2_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1151,plain,
% 2.64/1.01      ( k7_relset_1(X0_53,X1_53,X0_52,X2_53) = k9_relat_1(X0_52,X2_53)
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1493,plain,
% 2.64/1.01      ( k7_relset_1(sK0,sK0,sK2,X0_53) = k9_relat_1(sK2,X0_53) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1151]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_22,negated_conjecture,
% 2.64/1.01      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 2.64/1.01      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 2.64/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_701,negated_conjecture,
% 2.64/1.01      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 2.64/1.01      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1539,plain,
% 2.64/1.01      ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
% 2.64/1.01      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1493,c_701]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1540,plain,
% 2.64/1.01      ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
% 2.64/1.01      | k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1539,c_1493]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_11,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.64/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_708,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.64/1.01      | k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1152,plain,
% 2.64/1.01      ( k8_relset_1(X0_53,X1_53,X0_52,X2_53) = k10_relat_1(X0_52,X2_53)
% 2.64/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1536,plain,
% 2.64/1.01      ( k8_relset_1(sK0,sK0,sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1159,c_1152]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1665,plain,
% 2.64/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 2.64/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1540,c_1536]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_7,plain,
% 2.64/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.64/1.01      | ~ v2_funct_1(X1)
% 2.64/1.01      | ~ v1_funct_1(X1)
% 2.64/1.01      | ~ v1_relat_1(X1)
% 2.64/1.01      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 2.64/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_23,negated_conjecture,
% 2.64/1.01      ( r1_tarski(sK1,sK0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_339,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 2.64/1.01      | k1_relat_1(X0) != sK0
% 2.64/1.01      | sK1 != X1 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_340,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k10_relat_1(X0,k9_relat_1(X0,sK1)) = sK1
% 2.64/1.01      | k1_relat_1(X0) != sK0 ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_339]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_694,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0_52)
% 2.64/1.01      | ~ v1_funct_1(X0_52)
% 2.64/1.01      | ~ v1_relat_1(X0_52)
% 2.64/1.01      | k10_relat_1(X0_52,k9_relat_1(X0_52,sK1)) = sK1
% 2.64/1.01      | k1_relat_1(X0_52) != sK0 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_340]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_795,plain,
% 2.64/1.01      ( ~ v2_funct_1(sK2)
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 2.64/1.01      | k1_relat_1(sK2) != sK0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_694]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_5,plain,
% 2.64/1.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 2.64/1.01      | ~ v1_funct_1(X1)
% 2.64/1.01      | ~ v1_relat_1(X1)
% 2.64/1.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 2.64/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_321,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 2.64/1.01      | k2_relat_1(X0) != sK0
% 2.64/1.01      | sK1 != X1 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_322,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k9_relat_1(X0,k10_relat_1(X0,sK1)) = sK1
% 2.64/1.01      | k2_relat_1(X0) != sK0 ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_321]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_695,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0_52)
% 2.64/1.01      | ~ v1_relat_1(X0_52)
% 2.64/1.01      | k9_relat_1(X0_52,k10_relat_1(X0_52,sK1)) = sK1
% 2.64/1.01      | k2_relat_1(X0_52) != sK0 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_322]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_792,plain,
% 2.64/1.01      ( ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 2.64/1.01      | k2_relat_1(sK2) != sK0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_695]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_767,plain,
% 2.64/1.01      ( ~ v3_funct_2(sK2,sK0,sK0)
% 2.64/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.64/1.01      | v2_funct_1(sK2)
% 2.64/1.01      | ~ v1_funct_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_707]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(contradiction,plain,
% 2.64/1.01      ( $false ),
% 2.64/1.01      inference(minisat,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_3624,c_1665,c_1371,c_798,c_795,c_792,c_767,c_92,c_24,
% 2.64/1.01                 c_25,c_27]) ).
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  ------                               Statistics
% 2.64/1.01  
% 2.64/1.01  ------ General
% 2.64/1.01  
% 2.64/1.01  abstr_ref_over_cycles:                  0
% 2.64/1.01  abstr_ref_under_cycles:                 0
% 2.64/1.01  gc_basic_clause_elim:                   0
% 2.64/1.01  forced_gc_time:                         0
% 2.64/1.01  parsing_time:                           0.011
% 2.64/1.01  unif_index_cands_time:                  0.
% 2.64/1.01  unif_index_add_time:                    0.
% 2.64/1.01  orderings_time:                         0.
% 2.64/1.01  out_proof_time:                         0.015
% 2.64/1.01  total_time:                             0.157
% 2.64/1.01  num_of_symbols:                         55
% 2.64/1.01  num_of_terms:                           4077
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing
% 2.64/1.01  
% 2.64/1.01  num_of_splits:                          0
% 2.64/1.01  num_of_split_atoms:                     0
% 2.64/1.01  num_of_reused_defs:                     0
% 2.64/1.01  num_eq_ax_congr_red:                    28
% 2.64/1.01  num_of_sem_filtered_clauses:            1
% 2.64/1.01  num_of_subtypes:                        3
% 2.64/1.01  monotx_restored_types:                  1
% 2.64/1.01  sat_num_of_epr_types:                   0
% 2.64/1.01  sat_num_of_non_cyclic_types:            0
% 2.64/1.01  sat_guarded_non_collapsed_types:        1
% 2.64/1.01  num_pure_diseq_elim:                    0
% 2.64/1.01  simp_replaced_by:                       0
% 2.64/1.01  res_preprocessed:                       128
% 2.64/1.01  prep_upred:                             0
% 2.64/1.01  prep_unflattend:                        8
% 2.64/1.01  smt_new_axioms:                         0
% 2.64/1.01  pred_elim_cands:                        6
% 2.64/1.01  pred_elim:                              4
% 2.64/1.01  pred_elim_cl:                           5
% 2.64/1.01  pred_elim_cycles:                       7
% 2.64/1.01  merged_defs:                            0
% 2.64/1.01  merged_defs_ncl:                        0
% 2.64/1.01  bin_hyper_res:                          0
% 2.64/1.01  prep_cycles:                            4
% 2.64/1.01  pred_elim_time:                         0.005
% 2.64/1.01  splitting_time:                         0.
% 2.64/1.01  sem_filter_time:                        0.
% 2.64/1.01  monotx_time:                            0.001
% 2.64/1.01  subtype_inf_time:                       0.002
% 2.64/1.01  
% 2.64/1.01  ------ Problem properties
% 2.64/1.01  
% 2.64/1.01  clauses:                                22
% 2.64/1.01  conjectures:                            5
% 2.64/1.01  epr:                                    3
% 2.64/1.01  horn:                                   22
% 2.64/1.01  ground:                                 5
% 2.64/1.01  unary:                                  5
% 2.64/1.01  binary:                                 5
% 2.64/1.01  lits:                                   68
% 2.64/1.01  lits_eq:                                14
% 2.64/1.01  fd_pure:                                0
% 2.64/1.01  fd_pseudo:                              0
% 2.64/1.01  fd_cond:                                0
% 2.64/1.01  fd_pseudo_cond:                         1
% 2.64/1.01  ac_symbols:                             0
% 2.64/1.01  
% 2.64/1.01  ------ Propositional Solver
% 2.64/1.01  
% 2.64/1.01  prop_solver_calls:                      30
% 2.64/1.01  prop_fast_solver_calls:                 999
% 2.64/1.01  smt_solver_calls:                       0
% 2.64/1.01  smt_fast_solver_calls:                  0
% 2.64/1.01  prop_num_of_clauses:                    1290
% 2.64/1.01  prop_preprocess_simplified:             4832
% 2.64/1.01  prop_fo_subsumed:                       39
% 2.64/1.01  prop_solver_time:                       0.
% 2.64/1.01  smt_solver_time:                        0.
% 2.64/1.01  smt_fast_solver_time:                   0.
% 2.64/1.01  prop_fast_solver_time:                  0.
% 2.64/1.01  prop_unsat_core_time:                   0.
% 2.64/1.01  
% 2.64/1.01  ------ QBF
% 2.64/1.01  
% 2.64/1.01  qbf_q_res:                              0
% 2.64/1.01  qbf_num_tautologies:                    0
% 2.64/1.01  qbf_prep_cycles:                        0
% 2.64/1.01  
% 2.64/1.01  ------ BMC1
% 2.64/1.01  
% 2.64/1.01  bmc1_current_bound:                     -1
% 2.64/1.01  bmc1_last_solved_bound:                 -1
% 2.64/1.01  bmc1_unsat_core_size:                   -1
% 2.64/1.01  bmc1_unsat_core_parents_size:           -1
% 2.64/1.01  bmc1_merge_next_fun:                    0
% 2.64/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation
% 2.64/1.01  
% 2.64/1.01  inst_num_of_clauses:                    448
% 2.64/1.01  inst_num_in_passive:                    88
% 2.64/1.01  inst_num_in_active:                     258
% 2.64/1.01  inst_num_in_unprocessed:                102
% 2.64/1.01  inst_num_of_loops:                      280
% 2.64/1.01  inst_num_of_learning_restarts:          0
% 2.64/1.01  inst_num_moves_active_passive:          17
% 2.64/1.01  inst_lit_activity:                      0
% 2.64/1.01  inst_lit_activity_moves:                0
% 2.64/1.01  inst_num_tautologies:                   0
% 2.64/1.01  inst_num_prop_implied:                  0
% 2.64/1.01  inst_num_existing_simplified:           0
% 2.64/1.01  inst_num_eq_res_simplified:             0
% 2.64/1.01  inst_num_child_elim:                    0
% 2.64/1.01  inst_num_of_dismatching_blockings:      115
% 2.64/1.01  inst_num_of_non_proper_insts:           405
% 2.64/1.01  inst_num_of_duplicates:                 0
% 2.64/1.01  inst_inst_num_from_inst_to_res:         0
% 2.64/1.01  inst_dismatching_checking_time:         0.
% 2.64/1.01  
% 2.64/1.01  ------ Resolution
% 2.64/1.01  
% 2.64/1.01  res_num_of_clauses:                     0
% 2.64/1.01  res_num_in_passive:                     0
% 2.64/1.01  res_num_in_active:                      0
% 2.64/1.01  res_num_of_loops:                       132
% 2.64/1.01  res_forward_subset_subsumed:            37
% 2.64/1.01  res_backward_subset_subsumed:           0
% 2.64/1.01  res_forward_subsumed:                   0
% 2.64/1.01  res_backward_subsumed:                  0
% 2.64/1.01  res_forward_subsumption_resolution:     1
% 2.64/1.01  res_backward_subsumption_resolution:    0
% 2.64/1.01  res_clause_to_clause_subsumption:       94
% 2.64/1.01  res_orphan_elimination:                 0
% 2.64/1.01  res_tautology_del:                      68
% 2.64/1.01  res_num_eq_res_simplified:              0
% 2.64/1.01  res_num_sel_changes:                    0
% 2.64/1.01  res_moves_from_active_to_pass:          0
% 2.64/1.01  
% 2.64/1.01  ------ Superposition
% 2.64/1.01  
% 2.64/1.01  sup_time_total:                         0.
% 2.64/1.01  sup_time_generating:                    0.
% 2.64/1.01  sup_time_sim_full:                      0.
% 2.64/1.01  sup_time_sim_immed:                     0.
% 2.64/1.01  
% 2.64/1.01  sup_num_of_clauses:                     71
% 2.64/1.01  sup_num_in_active:                      50
% 2.64/1.01  sup_num_in_passive:                     21
% 2.64/1.01  sup_num_of_loops:                       55
% 2.64/1.01  sup_fw_superposition:                   21
% 2.64/1.01  sup_bw_superposition:                   31
% 2.64/1.01  sup_immediate_simplified:               10
% 2.64/1.01  sup_given_eliminated:                   0
% 2.64/1.01  comparisons_done:                       0
% 2.64/1.01  comparisons_avoided:                    0
% 2.64/1.01  
% 2.64/1.01  ------ Simplifications
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  sim_fw_subset_subsumed:                 0
% 2.64/1.01  sim_bw_subset_subsumed:                 0
% 2.64/1.01  sim_fw_subsumed:                        0
% 2.64/1.01  sim_bw_subsumed:                        0
% 2.64/1.01  sim_fw_subsumption_res:                 1
% 2.64/1.01  sim_bw_subsumption_res:                 0
% 2.64/1.01  sim_tautology_del:                      0
% 2.64/1.01  sim_eq_tautology_del:                   0
% 2.64/1.01  sim_eq_res_simp:                        0
% 2.64/1.01  sim_fw_demodulated:                     4
% 2.64/1.01  sim_bw_demodulated:                     5
% 2.64/1.01  sim_light_normalised:                   9
% 2.64/1.01  sim_joinable_taut:                      0
% 2.64/1.01  sim_joinable_simp:                      0
% 2.64/1.01  sim_ac_normalised:                      0
% 2.64/1.01  sim_smt_subsumption:                    0
% 2.64/1.01  
%------------------------------------------------------------------------------
