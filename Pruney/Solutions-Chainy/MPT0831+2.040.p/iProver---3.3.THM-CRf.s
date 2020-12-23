%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:42 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 154 expanded)
%              Number of clauses        :   72 (  80 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 430 expanded)
%              Number of equality atoms :   92 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f30])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f47,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_44,X0_45)
    | m1_subset_1(X1_44,X1_45)
    | X1_45 != X0_45
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_956,plain,
    ( m1_subset_1(X0_44,X0_45)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | X0_45 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | X0_44 != sK3 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1001,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | X0_44 != sK3 ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_3392,plain,
    ( m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_5])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,X0_46) = X0_44 ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_2006,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_595,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ r1_tarski(k1_relat_1(X0_44),X0_46)
    | ~ r1_tarski(k2_relat_1(X0_44),X1_46)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1372,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_46)))
    | ~ r1_tarski(k1_relat_1(X0_44),sK2)
    | ~ r1_tarski(k2_relat_1(X0_44),X0_46)
    | ~ v1_relat_1(X0_44) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_1749,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_611,plain,
    ( k1_relat_1(X0_44) = k1_relat_1(X1_44)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_1538,plain,
    ( k1_relat_1(X0_44) = k1_relat_1(k7_relat_1(X1_44,X0_46))
    | X0_44 != k7_relat_1(X1_44,X0_46) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_1543,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k7_relat_1(sK3,sK1))
    | sK3 != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1199,plain,
    ( r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X0_44,X2_46)),X2_46)
    | X1_46 != X2_46
    | X0_46 != k1_relat_1(k7_relat_1(X0_44,X2_46)) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1537,plain,
    ( r1_tarski(k1_relat_1(X0_44),X0_46)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X1_44,X1_46)),X1_46)
    | X0_46 != X1_46
    | k1_relat_1(X0_44) != k1_relat_1(k7_relat_1(X1_44,X1_46)) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_1540,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | r1_tarski(k1_relat_1(sK3),sK1)
    | k1_relat_1(sK3) != k1_relat_1(k7_relat_1(sK3,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK1) = sK3 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_600,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(X2_46,X0_46)
    | r1_tarski(X2_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_934,plain,
    ( r1_tarski(X0_46,sK2)
    | ~ r1_tarski(X0_46,sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1375,plain,
    ( r1_tarski(k1_relat_1(X0_44),sK2)
    | ~ r1_tarski(k1_relat_1(X0_44),sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_1381,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_605,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1322,plain,
    ( k7_relat_1(sK3,X0_46) != X0_44
    | sK3 != X0_44
    | sK3 = k7_relat_1(sK3,X0_46) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1323,plain,
    ( k7_relat_1(sK3,sK1) != sK3
    | sK3 = k7_relat_1(sK3,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | r1_tarski(k2_relat_1(X0_44),X1_46)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_1013,plain,
    ( X0_44 != X1_44
    | k5_relset_1(sK1,sK0,sK3,sK2) != X1_44
    | k5_relset_1(sK1,sK0,sK3,sK2) = X0_44 ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1110,plain,
    ( X0_44 != k7_relat_1(sK3,sK2)
    | k5_relset_1(sK1,sK0,sK3,sK2) = X0_44
    | k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1111,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k5_relset_1(sK1,sK0,sK3,sK2) = sK3
    | sK3 != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1045,plain,
    ( k7_relat_1(sK3,sK2) != X0_44
    | sK3 != X0_44
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1046,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK3 = k7_relat_1(sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_598,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1040,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_593,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_840,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ v1_relat_1(X1_44)
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_834,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_1029,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_834])).

cnf(c_1030,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1029])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k5_relset_1(X0_46,X1_46,X0_44,X2_46) = k7_relat_1(X0_44,X2_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_961,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k5_relset_1(sK1,sK0,sK3,X0_46) = k7_relat_1(sK3,X0_46) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k5_relset_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_976,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != X0_44
    | sK3 != X0_44
    | sK3 = k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1018,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2)
    | sK3 = k5_relset_1(sK1,sK0,sK3,sK2)
    | sK3 != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_603,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1002,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_203,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_591,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_597,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X0_46)),X0_46)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_628,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_604,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_623,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_602,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_621,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3392,c_2006,c_1749,c_1543,c_1540,c_1391,c_1381,c_1323,c_1298,c_1111,c_1046,c_1040,c_1030,c_1019,c_1018,c_1002,c_591,c_628,c_623,c_621,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:58:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/0.99  
% 1.84/0.99  ------  iProver source info
% 1.84/0.99  
% 1.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/0.99  git: non_committed_changes: false
% 1.84/0.99  git: last_make_outside_of_git: false
% 1.84/0.99  
% 1.84/0.99  ------ 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options
% 1.84/0.99  
% 1.84/0.99  --out_options                           all
% 1.84/0.99  --tptp_safe_out                         true
% 1.84/0.99  --problem_path                          ""
% 1.84/0.99  --include_path                          ""
% 1.84/0.99  --clausifier                            res/vclausify_rel
% 1.84/0.99  --clausifier_options                    --mode clausify
% 1.84/0.99  --stdin                                 false
% 1.84/0.99  --stats_out                             all
% 1.84/0.99  
% 1.84/0.99  ------ General Options
% 1.84/0.99  
% 1.84/0.99  --fof                                   false
% 1.84/0.99  --time_out_real                         305.
% 1.84/0.99  --time_out_virtual                      -1.
% 1.84/0.99  --symbol_type_check                     false
% 1.84/0.99  --clausify_out                          false
% 1.84/0.99  --sig_cnt_out                           false
% 1.84/0.99  --trig_cnt_out                          false
% 1.84/0.99  --trig_cnt_out_tolerance                1.
% 1.84/0.99  --trig_cnt_out_sk_spl                   false
% 1.84/0.99  --abstr_cl_out                          false
% 1.84/0.99  
% 1.84/0.99  ------ Global Options
% 1.84/0.99  
% 1.84/0.99  --schedule                              default
% 1.84/0.99  --add_important_lit                     false
% 1.84/0.99  --prop_solver_per_cl                    1000
% 1.84/0.99  --min_unsat_core                        false
% 1.84/0.99  --soft_assumptions                      false
% 1.84/0.99  --soft_lemma_size                       3
% 1.84/0.99  --prop_impl_unit_size                   0
% 1.84/0.99  --prop_impl_unit                        []
% 1.84/0.99  --share_sel_clauses                     true
% 1.84/0.99  --reset_solvers                         false
% 1.84/0.99  --bc_imp_inh                            [conj_cone]
% 1.84/0.99  --conj_cone_tolerance                   3.
% 1.84/0.99  --extra_neg_conj                        none
% 1.84/0.99  --large_theory_mode                     true
% 1.84/0.99  --prolific_symb_bound                   200
% 1.84/0.99  --lt_threshold                          2000
% 1.84/0.99  --clause_weak_htbl                      true
% 1.84/0.99  --gc_record_bc_elim                     false
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing Options
% 1.84/0.99  
% 1.84/0.99  --preprocessing_flag                    true
% 1.84/0.99  --time_out_prep_mult                    0.1
% 1.84/0.99  --splitting_mode                        input
% 1.84/0.99  --splitting_grd                         true
% 1.84/0.99  --splitting_cvd                         false
% 1.84/0.99  --splitting_cvd_svl                     false
% 1.84/0.99  --splitting_nvd                         32
% 1.84/0.99  --sub_typing                            true
% 1.84/0.99  --prep_gs_sim                           true
% 1.84/0.99  --prep_unflatten                        true
% 1.84/0.99  --prep_res_sim                          true
% 1.84/0.99  --prep_upred                            true
% 1.84/0.99  --prep_sem_filter                       exhaustive
% 1.84/0.99  --prep_sem_filter_out                   false
% 1.84/0.99  --pred_elim                             true
% 1.84/0.99  --res_sim_input                         true
% 1.84/0.99  --eq_ax_congr_red                       true
% 1.84/0.99  --pure_diseq_elim                       true
% 1.84/0.99  --brand_transform                       false
% 1.84/0.99  --non_eq_to_eq                          false
% 1.84/0.99  --prep_def_merge                        true
% 1.84/0.99  --prep_def_merge_prop_impl              false
% 1.84/0.99  --prep_def_merge_mbd                    true
% 1.84/0.99  --prep_def_merge_tr_red                 false
% 1.84/0.99  --prep_def_merge_tr_cl                  false
% 1.84/0.99  --smt_preprocessing                     true
% 1.84/0.99  --smt_ac_axioms                         fast
% 1.84/0.99  --preprocessed_out                      false
% 1.84/0.99  --preprocessed_stats                    false
% 1.84/0.99  
% 1.84/0.99  ------ Abstraction refinement Options
% 1.84/0.99  
% 1.84/0.99  --abstr_ref                             []
% 1.84/0.99  --abstr_ref_prep                        false
% 1.84/0.99  --abstr_ref_until_sat                   false
% 1.84/0.99  --abstr_ref_sig_restrict                funpre
% 1.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.99  --abstr_ref_under                       []
% 1.84/0.99  
% 1.84/0.99  ------ SAT Options
% 1.84/0.99  
% 1.84/0.99  --sat_mode                              false
% 1.84/0.99  --sat_fm_restart_options                ""
% 1.84/0.99  --sat_gr_def                            false
% 1.84/0.99  --sat_epr_types                         true
% 1.84/0.99  --sat_non_cyclic_types                  false
% 1.84/0.99  --sat_finite_models                     false
% 1.84/0.99  --sat_fm_lemmas                         false
% 1.84/0.99  --sat_fm_prep                           false
% 1.84/0.99  --sat_fm_uc_incr                        true
% 1.84/0.99  --sat_out_model                         small
% 1.84/0.99  --sat_out_clauses                       false
% 1.84/0.99  
% 1.84/0.99  ------ QBF Options
% 1.84/0.99  
% 1.84/0.99  --qbf_mode                              false
% 1.84/0.99  --qbf_elim_univ                         false
% 1.84/0.99  --qbf_dom_inst                          none
% 1.84/0.99  --qbf_dom_pre_inst                      false
% 1.84/0.99  --qbf_sk_in                             false
% 1.84/0.99  --qbf_pred_elim                         true
% 1.84/0.99  --qbf_split                             512
% 1.84/0.99  
% 1.84/0.99  ------ BMC1 Options
% 1.84/0.99  
% 1.84/0.99  --bmc1_incremental                      false
% 1.84/0.99  --bmc1_axioms                           reachable_all
% 1.84/0.99  --bmc1_min_bound                        0
% 1.84/0.99  --bmc1_max_bound                        -1
% 1.84/0.99  --bmc1_max_bound_default                -1
% 1.84/0.99  --bmc1_symbol_reachability              true
% 1.84/0.99  --bmc1_property_lemmas                  false
% 1.84/0.99  --bmc1_k_induction                      false
% 1.84/0.99  --bmc1_non_equiv_states                 false
% 1.84/0.99  --bmc1_deadlock                         false
% 1.84/0.99  --bmc1_ucm                              false
% 1.84/0.99  --bmc1_add_unsat_core                   none
% 1.84/0.99  --bmc1_unsat_core_children              false
% 1.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.99  --bmc1_out_stat                         full
% 1.84/0.99  --bmc1_ground_init                      false
% 1.84/0.99  --bmc1_pre_inst_next_state              false
% 1.84/0.99  --bmc1_pre_inst_state                   false
% 1.84/0.99  --bmc1_pre_inst_reach_state             false
% 1.84/0.99  --bmc1_out_unsat_core                   false
% 1.84/0.99  --bmc1_aig_witness_out                  false
% 1.84/0.99  --bmc1_verbose                          false
% 1.84/0.99  --bmc1_dump_clauses_tptp                false
% 1.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.99  --bmc1_dump_file                        -
% 1.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.99  --bmc1_ucm_extend_mode                  1
% 1.84/0.99  --bmc1_ucm_init_mode                    2
% 1.84/0.99  --bmc1_ucm_cone_mode                    none
% 1.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.99  --bmc1_ucm_relax_model                  4
% 1.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.99  --bmc1_ucm_layered_model                none
% 1.84/0.99  --bmc1_ucm_max_lemma_size               10
% 1.84/0.99  
% 1.84/0.99  ------ AIG Options
% 1.84/0.99  
% 1.84/0.99  --aig_mode                              false
% 1.84/0.99  
% 1.84/0.99  ------ Instantiation Options
% 1.84/0.99  
% 1.84/0.99  --instantiation_flag                    true
% 1.84/0.99  --inst_sos_flag                         false
% 1.84/0.99  --inst_sos_phase                        true
% 1.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel_side                     num_symb
% 1.84/0.99  --inst_solver_per_active                1400
% 1.84/0.99  --inst_solver_calls_frac                1.
% 1.84/0.99  --inst_passive_queue_type               priority_queues
% 1.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.99  --inst_passive_queues_freq              [25;2]
% 1.84/0.99  --inst_dismatching                      true
% 1.84/0.99  --inst_eager_unprocessed_to_passive     true
% 1.84/0.99  --inst_prop_sim_given                   true
% 1.84/0.99  --inst_prop_sim_new                     false
% 1.84/0.99  --inst_subs_new                         false
% 1.84/0.99  --inst_eq_res_simp                      false
% 1.84/0.99  --inst_subs_given                       false
% 1.84/0.99  --inst_orphan_elimination               true
% 1.84/0.99  --inst_learning_loop_flag               true
% 1.84/0.99  --inst_learning_start                   3000
% 1.84/0.99  --inst_learning_factor                  2
% 1.84/0.99  --inst_start_prop_sim_after_learn       3
% 1.84/0.99  --inst_sel_renew                        solver
% 1.84/0.99  --inst_lit_activity_flag                true
% 1.84/0.99  --inst_restr_to_given                   false
% 1.84/0.99  --inst_activity_threshold               500
% 1.84/0.99  --inst_out_proof                        true
% 1.84/0.99  
% 1.84/0.99  ------ Resolution Options
% 1.84/0.99  
% 1.84/0.99  --resolution_flag                       true
% 1.84/0.99  --res_lit_sel                           adaptive
% 1.84/0.99  --res_lit_sel_side                      none
% 1.84/0.99  --res_ordering                          kbo
% 1.84/0.99  --res_to_prop_solver                    active
% 1.84/0.99  --res_prop_simpl_new                    false
% 1.84/0.99  --res_prop_simpl_given                  true
% 1.84/0.99  --res_passive_queue_type                priority_queues
% 1.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.99  --res_passive_queues_freq               [15;5]
% 1.84/0.99  --res_forward_subs                      full
% 1.84/0.99  --res_backward_subs                     full
% 1.84/0.99  --res_forward_subs_resolution           true
% 1.84/0.99  --res_backward_subs_resolution          true
% 1.84/0.99  --res_orphan_elimination                true
% 1.84/0.99  --res_time_limit                        2.
% 1.84/0.99  --res_out_proof                         true
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Options
% 1.84/0.99  
% 1.84/0.99  --superposition_flag                    true
% 1.84/0.99  --sup_passive_queue_type                priority_queues
% 1.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.99  --demod_completeness_check              fast
% 1.84/0.99  --demod_use_ground                      true
% 1.84/0.99  --sup_to_prop_solver                    passive
% 1.84/0.99  --sup_prop_simpl_new                    true
% 1.84/0.99  --sup_prop_simpl_given                  true
% 1.84/0.99  --sup_fun_splitting                     false
% 1.84/0.99  --sup_smt_interval                      50000
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Simplification Setup
% 1.84/0.99  
% 1.84/0.99  --sup_indices_passive                   []
% 1.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_full_bw                           [BwDemod]
% 1.84/0.99  --sup_immed_triv                        [TrivRules]
% 1.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_immed_bw_main                     []
% 1.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  
% 1.84/0.99  ------ Combination Options
% 1.84/0.99  
% 1.84/0.99  --comb_res_mult                         3
% 1.84/0.99  --comb_sup_mult                         2
% 1.84/0.99  --comb_inst_mult                        10
% 1.84/0.99  
% 1.84/0.99  ------ Debug Options
% 1.84/0.99  
% 1.84/0.99  --dbg_backtrace                         false
% 1.84/0.99  --dbg_dump_prop_clauses                 false
% 1.84/0.99  --dbg_dump_prop_clauses_file            -
% 1.84/0.99  --dbg_out_stat                          false
% 1.84/0.99  ------ Parsing...
% 1.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.84/0.99  ------ Proving...
% 1.84/0.99  ------ Problem Properties 
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  clauses                                 11
% 1.84/0.99  conjectures                             2
% 1.84/0.99  EPR                                     2
% 1.84/0.99  Horn                                    11
% 1.84/0.99  unary                                   3
% 1.84/0.99  binary                                  3
% 1.84/0.99  lits                                    25
% 1.84/0.99  lits eq                                 3
% 1.84/0.99  fd_pure                                 0
% 1.84/0.99  fd_pseudo                               0
% 1.84/0.99  fd_cond                                 0
% 1.84/0.99  fd_pseudo_cond                          0
% 1.84/0.99  AC symbols                              0
% 1.84/0.99  
% 1.84/0.99  ------ Schedule dynamic 5 is on 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  ------ 
% 1.84/0.99  Current options:
% 1.84/0.99  ------ 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options
% 1.84/0.99  
% 1.84/0.99  --out_options                           all
% 1.84/0.99  --tptp_safe_out                         true
% 1.84/0.99  --problem_path                          ""
% 1.84/0.99  --include_path                          ""
% 1.84/0.99  --clausifier                            res/vclausify_rel
% 1.84/0.99  --clausifier_options                    --mode clausify
% 1.84/0.99  --stdin                                 false
% 1.84/0.99  --stats_out                             all
% 1.84/0.99  
% 1.84/0.99  ------ General Options
% 1.84/0.99  
% 1.84/0.99  --fof                                   false
% 1.84/0.99  --time_out_real                         305.
% 1.84/0.99  --time_out_virtual                      -1.
% 1.84/0.99  --symbol_type_check                     false
% 1.84/0.99  --clausify_out                          false
% 1.84/0.99  --sig_cnt_out                           false
% 1.84/0.99  --trig_cnt_out                          false
% 1.84/0.99  --trig_cnt_out_tolerance                1.
% 1.84/0.99  --trig_cnt_out_sk_spl                   false
% 1.84/0.99  --abstr_cl_out                          false
% 1.84/0.99  
% 1.84/0.99  ------ Global Options
% 1.84/0.99  
% 1.84/0.99  --schedule                              default
% 1.84/0.99  --add_important_lit                     false
% 1.84/0.99  --prop_solver_per_cl                    1000
% 1.84/0.99  --min_unsat_core                        false
% 1.84/0.99  --soft_assumptions                      false
% 1.84/0.99  --soft_lemma_size                       3
% 1.84/0.99  --prop_impl_unit_size                   0
% 1.84/0.99  --prop_impl_unit                        []
% 1.84/0.99  --share_sel_clauses                     true
% 1.84/0.99  --reset_solvers                         false
% 1.84/0.99  --bc_imp_inh                            [conj_cone]
% 1.84/0.99  --conj_cone_tolerance                   3.
% 1.84/0.99  --extra_neg_conj                        none
% 1.84/0.99  --large_theory_mode                     true
% 1.84/0.99  --prolific_symb_bound                   200
% 1.84/0.99  --lt_threshold                          2000
% 1.84/0.99  --clause_weak_htbl                      true
% 1.84/0.99  --gc_record_bc_elim                     false
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing Options
% 1.84/0.99  
% 1.84/0.99  --preprocessing_flag                    true
% 1.84/0.99  --time_out_prep_mult                    0.1
% 1.84/0.99  --splitting_mode                        input
% 1.84/0.99  --splitting_grd                         true
% 1.84/0.99  --splitting_cvd                         false
% 1.84/0.99  --splitting_cvd_svl                     false
% 1.84/0.99  --splitting_nvd                         32
% 1.84/0.99  --sub_typing                            true
% 1.84/0.99  --prep_gs_sim                           true
% 1.84/0.99  --prep_unflatten                        true
% 1.84/0.99  --prep_res_sim                          true
% 1.84/0.99  --prep_upred                            true
% 1.84/0.99  --prep_sem_filter                       exhaustive
% 1.84/0.99  --prep_sem_filter_out                   false
% 1.84/0.99  --pred_elim                             true
% 1.84/0.99  --res_sim_input                         true
% 1.84/0.99  --eq_ax_congr_red                       true
% 1.84/0.99  --pure_diseq_elim                       true
% 1.84/0.99  --brand_transform                       false
% 1.84/0.99  --non_eq_to_eq                          false
% 1.84/0.99  --prep_def_merge                        true
% 1.84/0.99  --prep_def_merge_prop_impl              false
% 1.84/0.99  --prep_def_merge_mbd                    true
% 1.84/0.99  --prep_def_merge_tr_red                 false
% 1.84/0.99  --prep_def_merge_tr_cl                  false
% 1.84/0.99  --smt_preprocessing                     true
% 1.84/0.99  --smt_ac_axioms                         fast
% 1.84/0.99  --preprocessed_out                      false
% 1.84/0.99  --preprocessed_stats                    false
% 1.84/0.99  
% 1.84/0.99  ------ Abstraction refinement Options
% 1.84/0.99  
% 1.84/0.99  --abstr_ref                             []
% 1.84/0.99  --abstr_ref_prep                        false
% 1.84/0.99  --abstr_ref_until_sat                   false
% 1.84/0.99  --abstr_ref_sig_restrict                funpre
% 1.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.99  --abstr_ref_under                       []
% 1.84/0.99  
% 1.84/0.99  ------ SAT Options
% 1.84/0.99  
% 1.84/0.99  --sat_mode                              false
% 1.84/0.99  --sat_fm_restart_options                ""
% 1.84/0.99  --sat_gr_def                            false
% 1.84/0.99  --sat_epr_types                         true
% 1.84/0.99  --sat_non_cyclic_types                  false
% 1.84/0.99  --sat_finite_models                     false
% 1.84/0.99  --sat_fm_lemmas                         false
% 1.84/0.99  --sat_fm_prep                           false
% 1.84/0.99  --sat_fm_uc_incr                        true
% 1.84/0.99  --sat_out_model                         small
% 1.84/0.99  --sat_out_clauses                       false
% 1.84/0.99  
% 1.84/0.99  ------ QBF Options
% 1.84/0.99  
% 1.84/0.99  --qbf_mode                              false
% 1.84/0.99  --qbf_elim_univ                         false
% 1.84/0.99  --qbf_dom_inst                          none
% 1.84/0.99  --qbf_dom_pre_inst                      false
% 1.84/0.99  --qbf_sk_in                             false
% 1.84/0.99  --qbf_pred_elim                         true
% 1.84/0.99  --qbf_split                             512
% 1.84/0.99  
% 1.84/0.99  ------ BMC1 Options
% 1.84/0.99  
% 1.84/0.99  --bmc1_incremental                      false
% 1.84/0.99  --bmc1_axioms                           reachable_all
% 1.84/0.99  --bmc1_min_bound                        0
% 1.84/0.99  --bmc1_max_bound                        -1
% 1.84/0.99  --bmc1_max_bound_default                -1
% 1.84/0.99  --bmc1_symbol_reachability              true
% 1.84/0.99  --bmc1_property_lemmas                  false
% 1.84/0.99  --bmc1_k_induction                      false
% 1.84/0.99  --bmc1_non_equiv_states                 false
% 1.84/0.99  --bmc1_deadlock                         false
% 1.84/0.99  --bmc1_ucm                              false
% 1.84/0.99  --bmc1_add_unsat_core                   none
% 1.84/0.99  --bmc1_unsat_core_children              false
% 1.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.99  --bmc1_out_stat                         full
% 1.84/0.99  --bmc1_ground_init                      false
% 1.84/0.99  --bmc1_pre_inst_next_state              false
% 1.84/0.99  --bmc1_pre_inst_state                   false
% 1.84/0.99  --bmc1_pre_inst_reach_state             false
% 1.84/0.99  --bmc1_out_unsat_core                   false
% 1.84/0.99  --bmc1_aig_witness_out                  false
% 1.84/0.99  --bmc1_verbose                          false
% 1.84/0.99  --bmc1_dump_clauses_tptp                false
% 1.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.99  --bmc1_dump_file                        -
% 1.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.99  --bmc1_ucm_extend_mode                  1
% 1.84/0.99  --bmc1_ucm_init_mode                    2
% 1.84/0.99  --bmc1_ucm_cone_mode                    none
% 1.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.99  --bmc1_ucm_relax_model                  4
% 1.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.99  --bmc1_ucm_layered_model                none
% 1.84/0.99  --bmc1_ucm_max_lemma_size               10
% 1.84/0.99  
% 1.84/0.99  ------ AIG Options
% 1.84/0.99  
% 1.84/0.99  --aig_mode                              false
% 1.84/0.99  
% 1.84/0.99  ------ Instantiation Options
% 1.84/0.99  
% 1.84/0.99  --instantiation_flag                    true
% 1.84/0.99  --inst_sos_flag                         false
% 1.84/0.99  --inst_sos_phase                        true
% 1.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel_side                     none
% 1.84/0.99  --inst_solver_per_active                1400
% 1.84/0.99  --inst_solver_calls_frac                1.
% 1.84/0.99  --inst_passive_queue_type               priority_queues
% 1.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.99  --inst_passive_queues_freq              [25;2]
% 1.84/0.99  --inst_dismatching                      true
% 1.84/0.99  --inst_eager_unprocessed_to_passive     true
% 1.84/0.99  --inst_prop_sim_given                   true
% 1.84/0.99  --inst_prop_sim_new                     false
% 1.84/0.99  --inst_subs_new                         false
% 1.84/0.99  --inst_eq_res_simp                      false
% 1.84/0.99  --inst_subs_given                       false
% 1.84/0.99  --inst_orphan_elimination               true
% 1.84/0.99  --inst_learning_loop_flag               true
% 1.84/0.99  --inst_learning_start                   3000
% 1.84/0.99  --inst_learning_factor                  2
% 1.84/0.99  --inst_start_prop_sim_after_learn       3
% 1.84/0.99  --inst_sel_renew                        solver
% 1.84/0.99  --inst_lit_activity_flag                true
% 1.84/0.99  --inst_restr_to_given                   false
% 1.84/0.99  --inst_activity_threshold               500
% 1.84/0.99  --inst_out_proof                        true
% 1.84/0.99  
% 1.84/0.99  ------ Resolution Options
% 1.84/0.99  
% 1.84/0.99  --resolution_flag                       false
% 1.84/0.99  --res_lit_sel                           adaptive
% 1.84/0.99  --res_lit_sel_side                      none
% 1.84/0.99  --res_ordering                          kbo
% 1.84/0.99  --res_to_prop_solver                    active
% 1.84/0.99  --res_prop_simpl_new                    false
% 1.84/0.99  --res_prop_simpl_given                  true
% 1.84/0.99  --res_passive_queue_type                priority_queues
% 1.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.99  --res_passive_queues_freq               [15;5]
% 1.84/0.99  --res_forward_subs                      full
% 1.84/0.99  --res_backward_subs                     full
% 1.84/0.99  --res_forward_subs_resolution           true
% 1.84/0.99  --res_backward_subs_resolution          true
% 1.84/0.99  --res_orphan_elimination                true
% 1.84/0.99  --res_time_limit                        2.
% 1.84/0.99  --res_out_proof                         true
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Options
% 1.84/0.99  
% 1.84/0.99  --superposition_flag                    true
% 1.84/0.99  --sup_passive_queue_type                priority_queues
% 1.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.99  --demod_completeness_check              fast
% 1.84/0.99  --demod_use_ground                      true
% 1.84/0.99  --sup_to_prop_solver                    passive
% 1.84/0.99  --sup_prop_simpl_new                    true
% 1.84/0.99  --sup_prop_simpl_given                  true
% 1.84/0.99  --sup_fun_splitting                     false
% 1.84/0.99  --sup_smt_interval                      50000
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Simplification Setup
% 1.84/0.99  
% 1.84/0.99  --sup_indices_passive                   []
% 1.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_full_bw                           [BwDemod]
% 1.84/0.99  --sup_immed_triv                        [TrivRules]
% 1.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_immed_bw_main                     []
% 1.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  
% 1.84/0.99  ------ Combination Options
% 1.84/0.99  
% 1.84/0.99  --comb_res_mult                         3
% 1.84/0.99  --comb_sup_mult                         2
% 1.84/0.99  --comb_inst_mult                        10
% 1.84/0.99  
% 1.84/0.99  ------ Debug Options
% 1.84/0.99  
% 1.84/0.99  --dbg_backtrace                         false
% 1.84/0.99  --dbg_dump_prop_clauses                 false
% 1.84/0.99  --dbg_dump_prop_clauses_file            -
% 1.84/0.99  --dbg_out_stat                          false
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  ------ Proving...
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  % SZS status Theorem for theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  fof(f7,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f20,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.99    inference(ennf_transformation,[],[f7])).
% 1.84/0.99  
% 1.84/0.99  fof(f39,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f20])).
% 1.84/0.99  
% 1.84/0.99  fof(f5,axiom,(
% 1.84/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f17,plain,(
% 1.84/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.84/0.99    inference(ennf_transformation,[],[f5])).
% 1.84/0.99  
% 1.84/0.99  fof(f18,plain,(
% 1.84/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.84/0.99    inference(flattening,[],[f17])).
% 1.84/0.99  
% 1.84/0.99  fof(f37,plain,(
% 1.84/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f18])).
% 1.84/0.99  
% 1.84/0.99  fof(f10,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f24,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.84/0.99    inference(ennf_transformation,[],[f10])).
% 1.84/0.99  
% 1.84/0.99  fof(f25,plain,(
% 1.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.84/0.99    inference(flattening,[],[f24])).
% 1.84/0.99  
% 1.84/0.99  fof(f44,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f25])).
% 1.84/0.99  
% 1.84/0.99  fof(f1,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f13,plain,(
% 1.84/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.84/0.99    inference(ennf_transformation,[],[f1])).
% 1.84/0.99  
% 1.84/0.99  fof(f14,plain,(
% 1.84/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.84/0.99    inference(flattening,[],[f13])).
% 1.84/0.99  
% 1.84/0.99  fof(f32,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f14])).
% 1.84/0.99  
% 1.84/0.99  fof(f40,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f20])).
% 1.84/0.99  
% 1.84/0.99  fof(f3,axiom,(
% 1.84/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f16,plain,(
% 1.84/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.84/0.99    inference(ennf_transformation,[],[f3])).
% 1.84/0.99  
% 1.84/0.99  fof(f28,plain,(
% 1.84/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.84/0.99    inference(nnf_transformation,[],[f16])).
% 1.84/0.99  
% 1.84/0.99  fof(f34,plain,(
% 1.84/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f28])).
% 1.84/0.99  
% 1.84/0.99  fof(f4,axiom,(
% 1.84/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f36,plain,(
% 1.84/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f4])).
% 1.84/0.99  
% 1.84/0.99  fof(f11,conjecture,(
% 1.84/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f12,negated_conjecture,(
% 1.84/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.84/0.99    inference(negated_conjecture,[],[f11])).
% 1.84/0.99  
% 1.84/0.99  fof(f26,plain,(
% 1.84/0.99    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.84/0.99    inference(ennf_transformation,[],[f12])).
% 1.84/0.99  
% 1.84/0.99  fof(f27,plain,(
% 1.84/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.84/0.99    inference(flattening,[],[f26])).
% 1.84/0.99  
% 1.84/0.99  fof(f30,plain,(
% 1.84/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.84/0.99    introduced(choice_axiom,[])).
% 1.84/0.99  
% 1.84/0.99  fof(f31,plain,(
% 1.84/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f30])).
% 1.84/0.99  
% 1.84/0.99  fof(f45,plain,(
% 1.84/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.84/0.99    inference(cnf_transformation,[],[f31])).
% 1.84/0.99  
% 1.84/0.99  fof(f2,axiom,(
% 1.84/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f15,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.84/0.99    inference(ennf_transformation,[],[f2])).
% 1.84/0.99  
% 1.84/0.99  fof(f33,plain,(
% 1.84/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f15])).
% 1.84/0.99  
% 1.84/0.99  fof(f8,axiom,(
% 1.84/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f21,plain,(
% 1.84/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.99    inference(ennf_transformation,[],[f8])).
% 1.84/0.99  
% 1.84/0.99  fof(f41,plain,(
% 1.84/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f21])).
% 1.84/0.99  
% 1.84/0.99  fof(f9,axiom,(
% 1.84/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f22,plain,(
% 1.84/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.84/0.99    inference(ennf_transformation,[],[f9])).
% 1.84/0.99  
% 1.84/0.99  fof(f23,plain,(
% 1.84/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.99    inference(flattening,[],[f22])).
% 1.84/0.99  
% 1.84/0.99  fof(f29,plain,(
% 1.84/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.99    inference(nnf_transformation,[],[f23])).
% 1.84/0.99  
% 1.84/0.99  fof(f43,plain,(
% 1.84/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f29])).
% 1.84/0.99  
% 1.84/0.99  fof(f48,plain,(
% 1.84/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.99    inference(equality_resolution,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f47,plain,(
% 1.84/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 1.84/0.99    inference(cnf_transformation,[],[f31])).
% 1.84/0.99  
% 1.84/0.99  fof(f6,axiom,(
% 1.84/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f19,plain,(
% 1.84/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.84/0.99    inference(ennf_transformation,[],[f6])).
% 1.84/0.99  
% 1.84/0.99  fof(f38,plain,(
% 1.84/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f19])).
% 1.84/0.99  
% 1.84/0.99  fof(f46,plain,(
% 1.84/0.99    r1_tarski(sK1,sK2)),
% 1.84/0.99    inference(cnf_transformation,[],[f31])).
% 1.84/0.99  
% 1.84/0.99  cnf(c_609,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0_44,X0_45)
% 1.84/0.99      | m1_subset_1(X1_44,X1_45)
% 1.84/0.99      | X1_45 != X0_45
% 1.84/0.99      | X1_44 != X0_44 ),
% 1.84/0.99      theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_956,plain,
% 1.84/0.99      ( m1_subset_1(X0_44,X0_45)
% 1.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | X0_45 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.84/0.99      | X0_44 != sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_609]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1001,plain,
% 1.84/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.84/0.99      | X0_44 != sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_956]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_3392,plain,
% 1.84/0.99      ( m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1001]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_8,plain,
% 1.84/0.99      ( v4_relat_1(X0,X1)
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_5,plain,
% 1.84/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.84/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_182,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/0.99      | ~ v1_relat_1(X0)
% 1.84/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.84/0.99      inference(resolution,[status(thm)],[c_8,c_5]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_592,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.84/0.99      | ~ v1_relat_1(X0_44)
% 1.84/0.99      | k7_relat_1(X0_44,X0_46) = X0_44 ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_182]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_2006,plain,
% 1.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.84/0.99      | ~ v1_relat_1(sK3)
% 1.84/0.99      | k7_relat_1(sK3,sK2) = sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_592]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_12,plain,
% 1.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.84/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.84/0.99      | ~ v1_relat_1(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_595,plain,
% 1.84/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(X0_44),X0_46)
% 1.84/0.99      | ~ r1_tarski(k2_relat_1(X0_44),X1_46)
% 1.84/0.99      | ~ v1_relat_1(X0_44) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1372,plain,
% 1.84/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_46)))
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(X0_44),sK2)
% 1.84/0.99      | ~ r1_tarski(k2_relat_1(X0_44),X0_46)
% 1.84/0.99      | ~ v1_relat_1(X0_44) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_595]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1749,plain,
% 1.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK2)
% 1.84/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK0)
% 1.84/0.99      | ~ v1_relat_1(sK3) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1372]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_611,plain,
% 1.84/0.99      ( k1_relat_1(X0_44) = k1_relat_1(X1_44) | X0_44 != X1_44 ),
% 1.84/0.99      theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1538,plain,
% 1.84/0.99      ( k1_relat_1(X0_44) = k1_relat_1(k7_relat_1(X1_44,X0_46))
% 1.84/0.99      | X0_44 != k7_relat_1(X1_44,X0_46) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_611]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1543,plain,
% 1.84/0.99      ( k1_relat_1(sK3) = k1_relat_1(k7_relat_1(sK3,sK1))
% 1.84/0.99      | sK3 != k7_relat_1(sK3,sK1) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_606,plain,
% 1.84/0.99      ( ~ r1_tarski(X0_46,X1_46)
% 1.84/0.99      | r1_tarski(X2_46,X3_46)
% 1.84/0.99      | X2_46 != X0_46
% 1.84/0.99      | X3_46 != X1_46 ),
% 1.84/0.99      theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1199,plain,
% 1.84/0.99      ( r1_tarski(X0_46,X1_46)
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(k7_relat_1(X0_44,X2_46)),X2_46)
% 1.84/0.99      | X1_46 != X2_46
% 1.84/0.99      | X0_46 != k1_relat_1(k7_relat_1(X0_44,X2_46)) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_606]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1537,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(X0_44),X0_46)
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(k7_relat_1(X1_44,X1_46)),X1_46)
% 1.84/0.99      | X0_46 != X1_46
% 1.84/0.99      | k1_relat_1(X0_44) != k1_relat_1(k7_relat_1(X1_44,X1_46)) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1199]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1540,plain,
% 1.84/0.99      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
% 1.84/0.99      | r1_tarski(k1_relat_1(sK3),sK1)
% 1.84/0.99      | k1_relat_1(sK3) != k1_relat_1(k7_relat_1(sK3,sK1))
% 1.84/0.99      | sK1 != sK1 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1391,plain,
% 1.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | ~ v1_relat_1(sK3)
% 1.84/0.99      | k7_relat_1(sK3,sK1) = sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_592]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_0,plain,
% 1.84/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.84/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_600,plain,
% 1.84/0.99      ( ~ r1_tarski(X0_46,X1_46)
% 1.84/0.99      | ~ r1_tarski(X2_46,X0_46)
% 1.84/0.99      | r1_tarski(X2_46,X1_46) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_934,plain,
% 1.84/0.99      ( r1_tarski(X0_46,sK2)
% 1.84/0.99      | ~ r1_tarski(X0_46,sK1)
% 1.84/0.99      | ~ r1_tarski(sK1,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_600]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1375,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(X0_44),sK2)
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(X0_44),sK1)
% 1.84/0.99      | ~ r1_tarski(sK1,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_934]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1381,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(sK3),sK2)
% 1.84/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 1.84/0.99      | ~ r1_tarski(sK1,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1375]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_605,plain,
% 1.84/0.99      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 1.84/0.99      theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1322,plain,
% 1.84/0.99      ( k7_relat_1(sK3,X0_46) != X0_44
% 1.84/0.99      | sK3 != X0_44
% 1.84/0.99      | sK3 = k7_relat_1(sK3,X0_46) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1323,plain,
% 1.84/0.99      ( k7_relat_1(sK3,sK1) != sK3
% 1.84/0.99      | sK3 = k7_relat_1(sK3,sK1)
% 1.84/0.99      | sK3 != sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1322]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_7,plain,
% 1.84/0.99      ( v5_relat_1(X0,X1)
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_3,plain,
% 1.84/0.99      ( ~ v5_relat_1(X0,X1)
% 1.84/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 1.84/0.99      | ~ v1_relat_1(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_215,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 1.84/0.99      | ~ v1_relat_1(X0) ),
% 1.84/0.99      inference(resolution,[status(thm)],[c_7,c_3]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_590,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.84/0.99      | r1_tarski(k2_relat_1(X0_44),X1_46)
% 1.84/0.99      | ~ v1_relat_1(X0_44) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_215]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1298,plain,
% 1.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | r1_tarski(k2_relat_1(sK3),sK0)
% 1.84/0.99      | ~ v1_relat_1(sK3) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_590]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1013,plain,
% 1.84/0.99      ( X0_44 != X1_44
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != X1_44
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) = X0_44 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1110,plain,
% 1.84/0.99      ( X0_44 != k7_relat_1(sK3,sK2)
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) = X0_44
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1111,plain,
% 1.84/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2)
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) = sK3
% 1.84/0.99      | sK3 != k7_relat_1(sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1110]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1045,plain,
% 1.84/0.99      ( k7_relat_1(sK3,sK2) != X0_44
% 1.84/0.99      | sK3 != X0_44
% 1.84/0.99      | sK3 = k7_relat_1(sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1046,plain,
% 1.84/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 1.84/0.99      | sK3 = k7_relat_1(sK3,sK2)
% 1.84/0.99      | sK3 != sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_1045]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_4,plain,
% 1.84/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.84/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_598,plain,
% 1.84/0.99      ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1040,plain,
% 1.84/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_598]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_15,negated_conjecture,
% 1.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_593,negated_conjecture,
% 1.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_840,plain,
% 1.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.84/0.99      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.84/0.99      | ~ v1_relat_1(X1)
% 1.84/0.99      | v1_relat_1(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_599,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 1.84/0.99      | ~ v1_relat_1(X1_44)
% 1.84/0.99      | v1_relat_1(X0_44) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_834,plain,
% 1.84/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 1.84/0.99      | v1_relat_1(X1_44) != iProver_top
% 1.84/0.99      | v1_relat_1(X0_44) = iProver_top ),
% 1.84/0.99      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1029,plain,
% 1.84/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 1.84/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.84/0.99      inference(superposition,[status(thm)],[c_840,c_834]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1030,plain,
% 1.84/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 1.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1029]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_9,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/0.99      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.84/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_596,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.84/0.99      | k5_relset_1(X0_46,X1_46,X0_44,X2_46) = k7_relat_1(X0_44,X2_46) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_961,plain,
% 1.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,X0_46) = k7_relat_1(sK3,X0_46) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_596]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1019,plain,
% 1.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_961]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_976,plain,
% 1.84/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != X0_44
% 1.84/0.99      | sK3 != X0_44
% 1.84/0.99      | sK3 = k5_relset_1(sK1,sK0,sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1018,plain,
% 1.84/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != k7_relat_1(sK3,sK2)
% 1.84/0.99      | sK3 = k5_relset_1(sK1,sK0,sK3,sK2)
% 1.84/0.99      | sK3 != k7_relat_1(sK3,sK2) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_976]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_603,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1002,plain,
% 1.84/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_603]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_10,plain,
% 1.84/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 1.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_13,negated_conjecture,
% 1.84/0.99      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 1.84/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_202,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 1.84/0.99      | sK3 != X0
% 1.84/0.99      | sK0 != X2
% 1.84/0.99      | sK1 != X1 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_203,plain,
% 1.84/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_202]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_591,plain,
% 1.84/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/0.99      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_203]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_6,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_597,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X0_46)),X0_46)
% 1.84/0.99      | ~ v1_relat_1(X0_44) ),
% 1.84/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_628,plain,
% 1.84/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
% 1.84/0.99      | ~ v1_relat_1(sK3) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_597]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_604,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_623,plain,
% 1.84/0.99      ( sK1 = sK1 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_604]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_602,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_621,plain,
% 1.84/0.99      ( sK3 = sK3 ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_602]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_14,negated_conjecture,
% 1.84/0.99      ( r1_tarski(sK1,sK2) ),
% 1.84/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(contradiction,plain,
% 1.84/0.99      ( $false ),
% 1.84/0.99      inference(minisat,
% 1.84/0.99                [status(thm)],
% 1.84/0.99                [c_3392,c_2006,c_1749,c_1543,c_1540,c_1391,c_1381,c_1323,
% 1.84/0.99                 c_1298,c_1111,c_1046,c_1040,c_1030,c_1019,c_1018,c_1002,
% 1.84/0.99                 c_591,c_628,c_623,c_621,c_14,c_15]) ).
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  ------                               Statistics
% 1.84/0.99  
% 1.84/0.99  ------ General
% 1.84/0.99  
% 1.84/0.99  abstr_ref_over_cycles:                  0
% 1.84/0.99  abstr_ref_under_cycles:                 0
% 1.84/0.99  gc_basic_clause_elim:                   0
% 1.84/0.99  forced_gc_time:                         0
% 1.84/0.99  parsing_time:                           0.009
% 1.84/0.99  unif_index_cands_time:                  0.
% 1.84/0.99  unif_index_add_time:                    0.
% 1.84/0.99  orderings_time:                         0.
% 1.84/0.99  out_proof_time:                         0.008
% 1.84/0.99  total_time:                             0.166
% 1.84/0.99  num_of_symbols:                         47
% 1.84/0.99  num_of_terms:                           4291
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing
% 1.84/0.99  
% 1.84/0.99  num_of_splits:                          0
% 1.84/0.99  num_of_split_atoms:                     0
% 1.84/0.99  num_of_reused_defs:                     0
% 1.84/0.99  num_eq_ax_congr_red:                    13
% 1.84/0.99  num_of_sem_filtered_clauses:            1
% 1.84/0.99  num_of_subtypes:                        3
% 1.84/0.99  monotx_restored_types:                  1
% 1.84/0.99  sat_num_of_epr_types:                   0
% 1.84/0.99  sat_num_of_non_cyclic_types:            0
% 1.84/0.99  sat_guarded_non_collapsed_types:        0
% 1.84/0.99  num_pure_diseq_elim:                    0
% 1.84/0.99  simp_replaced_by:                       0
% 1.84/0.99  res_preprocessed:                       72
% 1.84/0.99  prep_upred:                             0
% 1.84/0.99  prep_unflattend:                        19
% 1.84/0.99  smt_new_axioms:                         0
% 1.84/0.99  pred_elim_cands:                        3
% 1.84/0.99  pred_elim:                              3
% 1.84/0.99  pred_elim_cl:                           5
% 1.84/0.99  pred_elim_cycles:                       5
% 1.84/0.99  merged_defs:                            0
% 1.84/0.99  merged_defs_ncl:                        0
% 1.84/0.99  bin_hyper_res:                          0
% 1.84/0.99  prep_cycles:                            4
% 1.84/0.99  pred_elim_time:                         0.006
% 1.84/0.99  splitting_time:                         0.
% 1.84/0.99  sem_filter_time:                        0.
% 1.84/0.99  monotx_time:                            0.001
% 1.84/0.99  subtype_inf_time:                       0.001
% 1.84/0.99  
% 1.84/0.99  ------ Problem properties
% 1.84/0.99  
% 1.84/0.99  clauses:                                11
% 1.84/0.99  conjectures:                            2
% 1.84/0.99  epr:                                    2
% 1.84/0.99  horn:                                   11
% 1.84/0.99  ground:                                 3
% 1.84/0.99  unary:                                  3
% 1.84/0.99  binary:                                 3
% 1.84/0.99  lits:                                   25
% 1.84/0.99  lits_eq:                                3
% 1.84/0.99  fd_pure:                                0
% 1.84/0.99  fd_pseudo:                              0
% 1.84/0.99  fd_cond:                                0
% 1.84/0.99  fd_pseudo_cond:                         0
% 1.84/0.99  ac_symbols:                             0
% 1.84/0.99  
% 1.84/0.99  ------ Propositional Solver
% 1.84/0.99  
% 1.84/0.99  prop_solver_calls:                      29
% 1.84/0.99  prop_fast_solver_calls:                 544
% 1.84/0.99  smt_solver_calls:                       0
% 1.84/0.99  smt_fast_solver_calls:                  0
% 1.84/0.99  prop_num_of_clauses:                    1266
% 1.84/0.99  prop_preprocess_simplified:             3695
% 1.84/0.99  prop_fo_subsumed:                       6
% 1.84/0.99  prop_solver_time:                       0.
% 1.84/0.99  smt_solver_time:                        0.
% 1.84/0.99  smt_fast_solver_time:                   0.
% 1.84/0.99  prop_fast_solver_time:                  0.
% 1.84/0.99  prop_unsat_core_time:                   0.
% 1.84/0.99  
% 1.84/0.99  ------ QBF
% 1.84/0.99  
% 1.84/0.99  qbf_q_res:                              0
% 1.84/0.99  qbf_num_tautologies:                    0
% 1.84/0.99  qbf_prep_cycles:                        0
% 1.84/0.99  
% 1.84/0.99  ------ BMC1
% 1.84/0.99  
% 1.84/0.99  bmc1_current_bound:                     -1
% 1.84/0.99  bmc1_last_solved_bound:                 -1
% 1.84/0.99  bmc1_unsat_core_size:                   -1
% 1.84/0.99  bmc1_unsat_core_parents_size:           -1
% 1.84/0.99  bmc1_merge_next_fun:                    0
% 1.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.84/0.99  
% 1.84/0.99  ------ Instantiation
% 1.84/0.99  
% 1.84/0.99  inst_num_of_clauses:                    396
% 1.84/0.99  inst_num_in_passive:                    184
% 1.84/0.99  inst_num_in_active:                     207
% 1.84/0.99  inst_num_in_unprocessed:                4
% 1.84/0.99  inst_num_of_loops:                      232
% 1.84/0.99  inst_num_of_learning_restarts:          0
% 1.84/0.99  inst_num_moves_active_passive:          20
% 1.84/0.99  inst_lit_activity:                      0
% 1.84/0.99  inst_lit_activity_moves:                0
% 1.84/0.99  inst_num_tautologies:                   0
% 1.84/0.99  inst_num_prop_implied:                  0
% 1.84/0.99  inst_num_existing_simplified:           0
% 1.84/0.99  inst_num_eq_res_simplified:             0
% 1.84/0.99  inst_num_child_elim:                    0
% 1.84/0.99  inst_num_of_dismatching_blockings:      155
% 1.84/0.99  inst_num_of_non_proper_insts:           345
% 1.84/0.99  inst_num_of_duplicates:                 0
% 1.84/0.99  inst_inst_num_from_inst_to_res:         0
% 1.84/0.99  inst_dismatching_checking_time:         0.
% 1.84/0.99  
% 1.84/0.99  ------ Resolution
% 1.84/0.99  
% 1.84/0.99  res_num_of_clauses:                     0
% 1.84/0.99  res_num_in_passive:                     0
% 1.84/0.99  res_num_in_active:                      0
% 1.84/0.99  res_num_of_loops:                       76
% 1.84/0.99  res_forward_subset_subsumed:            44
% 1.84/0.99  res_backward_subset_subsumed:           0
% 1.84/0.99  res_forward_subsumed:                   0
% 1.84/0.99  res_backward_subsumed:                  0
% 1.84/0.99  res_forward_subsumption_resolution:     0
% 1.84/0.99  res_backward_subsumption_resolution:    0
% 1.84/0.99  res_clause_to_clause_subsumption:       169
% 1.84/0.99  res_orphan_elimination:                 0
% 1.84/0.99  res_tautology_del:                      70
% 1.84/0.99  res_num_eq_res_simplified:              0
% 1.84/0.99  res_num_sel_changes:                    0
% 1.84/0.99  res_moves_from_active_to_pass:          0
% 1.84/0.99  
% 1.84/0.99  ------ Superposition
% 1.84/0.99  
% 1.84/0.99  sup_time_total:                         0.
% 1.84/0.99  sup_time_generating:                    0.
% 1.84/0.99  sup_time_sim_full:                      0.
% 1.84/0.99  sup_time_sim_immed:                     0.
% 1.84/0.99  
% 1.84/0.99  sup_num_of_clauses:                     57
% 1.84/0.99  sup_num_in_active:                      45
% 1.84/0.99  sup_num_in_passive:                     12
% 1.84/0.99  sup_num_of_loops:                       46
% 1.84/0.99  sup_fw_superposition:                   25
% 1.84/0.99  sup_bw_superposition:                   44
% 1.84/0.99  sup_immediate_simplified:               2
% 1.84/0.99  sup_given_eliminated:                   0
% 1.84/0.99  comparisons_done:                       0
% 1.84/0.99  comparisons_avoided:                    0
% 1.84/0.99  
% 1.84/0.99  ------ Simplifications
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  sim_fw_subset_subsumed:                 2
% 1.84/0.99  sim_bw_subset_subsumed:                 6
% 1.84/0.99  sim_fw_subsumed:                        0
% 1.84/0.99  sim_bw_subsumed:                        0
% 1.84/0.99  sim_fw_subsumption_res:                 0
% 1.84/0.99  sim_bw_subsumption_res:                 0
% 1.84/0.99  sim_tautology_del:                      2
% 1.84/0.99  sim_eq_tautology_del:                   0
% 1.84/0.99  sim_eq_res_simp:                        0
% 1.84/0.99  sim_fw_demodulated:                     0
% 1.84/0.99  sim_bw_demodulated:                     1
% 1.84/0.99  sim_light_normalised:                   0
% 1.84/0.99  sim_joinable_taut:                      0
% 1.84/0.99  sim_joinable_simp:                      0
% 1.84/0.99  sim_ac_normalised:                      0
% 1.84/0.99  sim_smt_subsumption:                    0
% 1.84/0.99  
%------------------------------------------------------------------------------
