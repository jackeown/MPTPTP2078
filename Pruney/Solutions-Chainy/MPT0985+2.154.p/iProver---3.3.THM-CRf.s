%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:51 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  157 (1398 expanded)
%              Number of clauses        :   93 ( 545 expanded)
%              Number of leaves         :   16 ( 256 expanded)
%              Depth                    :   24
%              Number of atoms          :  449 (6151 expanded)
%              Number of equality atoms :  168 (1155 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f39])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1185,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1188,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2095,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1185,c_1188])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2097,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2095,c_23])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1630,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1194])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_207])).

cnf(c_1183,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_1852,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1183])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1193,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1861,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1852,c_1193])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_405,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_406,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_408,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_27])).

cnf(c_1179,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_1865,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1861,c_1179])).

cnf(c_2168,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2097,c_1865])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2242,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2168,c_1186])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_419,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_420,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_53,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_422,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_27,c_24,c_53])).

cnf(c_1178,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_1866,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1861,c_1178])).

cnf(c_2243,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2242,c_1866])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_58,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_60,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_61,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_63,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_2409,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_28,c_60,c_63,c_1861])).

cnf(c_2417,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,X0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_1194])).

cnf(c_3388,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,X0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_1183])).

cnf(c_3891,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3388,c_28,c_60,c_1861])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1196,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_386,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_6,c_10])).

cnf(c_1180,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_4440,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1180])).

cnf(c_4579,plain,
    ( k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3891,c_4440])).

cnf(c_4586,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK1) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4579,c_2168])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1192,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3896,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_3891,c_1192])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_433,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_434,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_438,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_27])).

cnf(c_1177,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1864,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1861,c_1177])).

cnf(c_3897,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_3896,c_1864])).

cnf(c_4711,plain,
    ( k10_relat_1(sK2,sK1) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4586,c_3897])).

cnf(c_4712,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4711,c_1866])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1187,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2804,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1185,c_1187])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2934,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_1189])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3037,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2934,c_30])).

cnf(c_3044,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3037,c_1194])).

cnf(c_4882,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_3044])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_341,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_342,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_1182,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_1949,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1865,c_1182])).

cnf(c_343,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_2324,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1949,c_28,c_60,c_63,c_343,c_1861,c_2168])).

cnf(c_2328,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2324,c_1866])).

cnf(c_2419,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2328])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4882,c_2419])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.70/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.00  
% 2.70/1.00  ------  iProver source info
% 2.70/1.00  
% 2.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.00  git: non_committed_changes: false
% 2.70/1.00  git: last_make_outside_of_git: false
% 2.70/1.00  
% 2.70/1.00  ------ 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options
% 2.70/1.00  
% 2.70/1.00  --out_options                           all
% 2.70/1.00  --tptp_safe_out                         true
% 2.70/1.00  --problem_path                          ""
% 2.70/1.00  --include_path                          ""
% 2.70/1.00  --clausifier                            res/vclausify_rel
% 2.70/1.00  --clausifier_options                    --mode clausify
% 2.70/1.00  --stdin                                 false
% 2.70/1.00  --stats_out                             all
% 2.70/1.00  
% 2.70/1.00  ------ General Options
% 2.70/1.00  
% 2.70/1.00  --fof                                   false
% 2.70/1.00  --time_out_real                         305.
% 2.70/1.00  --time_out_virtual                      -1.
% 2.70/1.00  --symbol_type_check                     false
% 2.70/1.00  --clausify_out                          false
% 2.70/1.00  --sig_cnt_out                           false
% 2.70/1.00  --trig_cnt_out                          false
% 2.70/1.00  --trig_cnt_out_tolerance                1.
% 2.70/1.00  --trig_cnt_out_sk_spl                   false
% 2.70/1.00  --abstr_cl_out                          false
% 2.70/1.00  
% 2.70/1.00  ------ Global Options
% 2.70/1.00  
% 2.70/1.00  --schedule                              default
% 2.70/1.00  --add_important_lit                     false
% 2.70/1.00  --prop_solver_per_cl                    1000
% 2.70/1.00  --min_unsat_core                        false
% 2.70/1.00  --soft_assumptions                      false
% 2.70/1.00  --soft_lemma_size                       3
% 2.70/1.00  --prop_impl_unit_size                   0
% 2.70/1.00  --prop_impl_unit                        []
% 2.70/1.00  --share_sel_clauses                     true
% 2.70/1.00  --reset_solvers                         false
% 2.70/1.00  --bc_imp_inh                            [conj_cone]
% 2.70/1.00  --conj_cone_tolerance                   3.
% 2.70/1.00  --extra_neg_conj                        none
% 2.70/1.00  --large_theory_mode                     true
% 2.70/1.00  --prolific_symb_bound                   200
% 2.70/1.00  --lt_threshold                          2000
% 2.70/1.00  --clause_weak_htbl                      true
% 2.70/1.00  --gc_record_bc_elim                     false
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing Options
% 2.70/1.00  
% 2.70/1.00  --preprocessing_flag                    true
% 2.70/1.00  --time_out_prep_mult                    0.1
% 2.70/1.00  --splitting_mode                        input
% 2.70/1.00  --splitting_grd                         true
% 2.70/1.00  --splitting_cvd                         false
% 2.70/1.00  --splitting_cvd_svl                     false
% 2.70/1.00  --splitting_nvd                         32
% 2.70/1.00  --sub_typing                            true
% 2.70/1.00  --prep_gs_sim                           true
% 2.70/1.00  --prep_unflatten                        true
% 2.70/1.00  --prep_res_sim                          true
% 2.70/1.00  --prep_upred                            true
% 2.70/1.00  --prep_sem_filter                       exhaustive
% 2.70/1.00  --prep_sem_filter_out                   false
% 2.70/1.00  --pred_elim                             true
% 2.70/1.00  --res_sim_input                         true
% 2.70/1.00  --eq_ax_congr_red                       true
% 2.70/1.00  --pure_diseq_elim                       true
% 2.70/1.00  --brand_transform                       false
% 2.70/1.00  --non_eq_to_eq                          false
% 2.70/1.00  --prep_def_merge                        true
% 2.70/1.00  --prep_def_merge_prop_impl              false
% 2.70/1.00  --prep_def_merge_mbd                    true
% 2.70/1.00  --prep_def_merge_tr_red                 false
% 2.70/1.00  --prep_def_merge_tr_cl                  false
% 2.70/1.00  --smt_preprocessing                     true
% 2.70/1.00  --smt_ac_axioms                         fast
% 2.70/1.00  --preprocessed_out                      false
% 2.70/1.00  --preprocessed_stats                    false
% 2.70/1.00  
% 2.70/1.00  ------ Abstraction refinement Options
% 2.70/1.00  
% 2.70/1.00  --abstr_ref                             []
% 2.70/1.00  --abstr_ref_prep                        false
% 2.70/1.00  --abstr_ref_until_sat                   false
% 2.70/1.00  --abstr_ref_sig_restrict                funpre
% 2.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.00  --abstr_ref_under                       []
% 2.70/1.00  
% 2.70/1.00  ------ SAT Options
% 2.70/1.00  
% 2.70/1.00  --sat_mode                              false
% 2.70/1.00  --sat_fm_restart_options                ""
% 2.70/1.00  --sat_gr_def                            false
% 2.70/1.00  --sat_epr_types                         true
% 2.70/1.00  --sat_non_cyclic_types                  false
% 2.70/1.00  --sat_finite_models                     false
% 2.70/1.00  --sat_fm_lemmas                         false
% 2.70/1.00  --sat_fm_prep                           false
% 2.70/1.00  --sat_fm_uc_incr                        true
% 2.70/1.00  --sat_out_model                         small
% 2.70/1.00  --sat_out_clauses                       false
% 2.70/1.00  
% 2.70/1.00  ------ QBF Options
% 2.70/1.00  
% 2.70/1.00  --qbf_mode                              false
% 2.70/1.00  --qbf_elim_univ                         false
% 2.70/1.00  --qbf_dom_inst                          none
% 2.70/1.00  --qbf_dom_pre_inst                      false
% 2.70/1.00  --qbf_sk_in                             false
% 2.70/1.00  --qbf_pred_elim                         true
% 2.70/1.00  --qbf_split                             512
% 2.70/1.00  
% 2.70/1.00  ------ BMC1 Options
% 2.70/1.00  
% 2.70/1.00  --bmc1_incremental                      false
% 2.70/1.00  --bmc1_axioms                           reachable_all
% 2.70/1.00  --bmc1_min_bound                        0
% 2.70/1.00  --bmc1_max_bound                        -1
% 2.70/1.00  --bmc1_max_bound_default                -1
% 2.70/1.00  --bmc1_symbol_reachability              true
% 2.70/1.00  --bmc1_property_lemmas                  false
% 2.70/1.00  --bmc1_k_induction                      false
% 2.70/1.00  --bmc1_non_equiv_states                 false
% 2.70/1.00  --bmc1_deadlock                         false
% 2.70/1.00  --bmc1_ucm                              false
% 2.70/1.00  --bmc1_add_unsat_core                   none
% 2.70/1.00  --bmc1_unsat_core_children              false
% 2.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.00  --bmc1_out_stat                         full
% 2.70/1.00  --bmc1_ground_init                      false
% 2.70/1.00  --bmc1_pre_inst_next_state              false
% 2.70/1.00  --bmc1_pre_inst_state                   false
% 2.70/1.00  --bmc1_pre_inst_reach_state             false
% 2.70/1.00  --bmc1_out_unsat_core                   false
% 2.70/1.00  --bmc1_aig_witness_out                  false
% 2.70/1.00  --bmc1_verbose                          false
% 2.70/1.00  --bmc1_dump_clauses_tptp                false
% 2.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.00  --bmc1_dump_file                        -
% 2.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.00  --bmc1_ucm_extend_mode                  1
% 2.70/1.00  --bmc1_ucm_init_mode                    2
% 2.70/1.00  --bmc1_ucm_cone_mode                    none
% 2.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.00  --bmc1_ucm_relax_model                  4
% 2.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.00  --bmc1_ucm_layered_model                none
% 2.70/1.00  --bmc1_ucm_max_lemma_size               10
% 2.70/1.00  
% 2.70/1.00  ------ AIG Options
% 2.70/1.00  
% 2.70/1.00  --aig_mode                              false
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation Options
% 2.70/1.00  
% 2.70/1.00  --instantiation_flag                    true
% 2.70/1.00  --inst_sos_flag                         false
% 2.70/1.00  --inst_sos_phase                        true
% 2.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel_side                     num_symb
% 2.70/1.00  --inst_solver_per_active                1400
% 2.70/1.00  --inst_solver_calls_frac                1.
% 2.70/1.00  --inst_passive_queue_type               priority_queues
% 2.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.00  --inst_passive_queues_freq              [25;2]
% 2.70/1.00  --inst_dismatching                      true
% 2.70/1.00  --inst_eager_unprocessed_to_passive     true
% 2.70/1.00  --inst_prop_sim_given                   true
% 2.70/1.00  --inst_prop_sim_new                     false
% 2.70/1.00  --inst_subs_new                         false
% 2.70/1.00  --inst_eq_res_simp                      false
% 2.70/1.00  --inst_subs_given                       false
% 2.70/1.00  --inst_orphan_elimination               true
% 2.70/1.00  --inst_learning_loop_flag               true
% 2.70/1.00  --inst_learning_start                   3000
% 2.70/1.00  --inst_learning_factor                  2
% 2.70/1.00  --inst_start_prop_sim_after_learn       3
% 2.70/1.00  --inst_sel_renew                        solver
% 2.70/1.00  --inst_lit_activity_flag                true
% 2.70/1.00  --inst_restr_to_given                   false
% 2.70/1.00  --inst_activity_threshold               500
% 2.70/1.00  --inst_out_proof                        true
% 2.70/1.00  
% 2.70/1.00  ------ Resolution Options
% 2.70/1.00  
% 2.70/1.00  --resolution_flag                       true
% 2.70/1.00  --res_lit_sel                           adaptive
% 2.70/1.00  --res_lit_sel_side                      none
% 2.70/1.00  --res_ordering                          kbo
% 2.70/1.00  --res_to_prop_solver                    active
% 2.70/1.00  --res_prop_simpl_new                    false
% 2.70/1.00  --res_prop_simpl_given                  true
% 2.70/1.00  --res_passive_queue_type                priority_queues
% 2.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.00  --res_passive_queues_freq               [15;5]
% 2.70/1.00  --res_forward_subs                      full
% 2.70/1.00  --res_backward_subs                     full
% 2.70/1.00  --res_forward_subs_resolution           true
% 2.70/1.00  --res_backward_subs_resolution          true
% 2.70/1.00  --res_orphan_elimination                true
% 2.70/1.00  --res_time_limit                        2.
% 2.70/1.00  --res_out_proof                         true
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Options
% 2.70/1.00  
% 2.70/1.00  --superposition_flag                    true
% 2.70/1.00  --sup_passive_queue_type                priority_queues
% 2.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.00  --demod_completeness_check              fast
% 2.70/1.00  --demod_use_ground                      true
% 2.70/1.00  --sup_to_prop_solver                    passive
% 2.70/1.00  --sup_prop_simpl_new                    true
% 2.70/1.00  --sup_prop_simpl_given                  true
% 2.70/1.00  --sup_fun_splitting                     false
% 2.70/1.00  --sup_smt_interval                      50000
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Simplification Setup
% 2.70/1.00  
% 2.70/1.00  --sup_indices_passive                   []
% 2.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_full_bw                           [BwDemod]
% 2.70/1.00  --sup_immed_triv                        [TrivRules]
% 2.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_immed_bw_main                     []
% 2.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  
% 2.70/1.00  ------ Combination Options
% 2.70/1.00  
% 2.70/1.00  --comb_res_mult                         3
% 2.70/1.00  --comb_sup_mult                         2
% 2.70/1.00  --comb_inst_mult                        10
% 2.70/1.00  
% 2.70/1.00  ------ Debug Options
% 2.70/1.00  
% 2.70/1.00  --dbg_backtrace                         false
% 2.70/1.00  --dbg_dump_prop_clauses                 false
% 2.70/1.00  --dbg_dump_prop_clauses_file            -
% 2.70/1.00  --dbg_out_stat                          false
% 2.70/1.00  ------ Parsing...
% 2.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.00  ------ Proving...
% 2.70/1.00  ------ Problem Properties 
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  clauses                                 22
% 2.70/1.00  conjectures                             3
% 2.70/1.00  EPR                                     4
% 2.70/1.00  Horn                                    22
% 2.70/1.00  unary                                   5
% 2.70/1.00  binary                                  9
% 2.70/1.00  lits                                    51
% 2.70/1.00  lits eq                                 12
% 2.70/1.00  fd_pure                                 0
% 2.70/1.00  fd_pseudo                               0
% 2.70/1.00  fd_cond                                 0
% 2.70/1.00  fd_pseudo_cond                          1
% 2.70/1.00  AC symbols                              0
% 2.70/1.00  
% 2.70/1.00  ------ Schedule dynamic 5 is on 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  ------ 
% 2.70/1.00  Current options:
% 2.70/1.00  ------ 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options
% 2.70/1.00  
% 2.70/1.00  --out_options                           all
% 2.70/1.00  --tptp_safe_out                         true
% 2.70/1.00  --problem_path                          ""
% 2.70/1.00  --include_path                          ""
% 2.70/1.00  --clausifier                            res/vclausify_rel
% 2.70/1.00  --clausifier_options                    --mode clausify
% 2.70/1.00  --stdin                                 false
% 2.70/1.00  --stats_out                             all
% 2.70/1.00  
% 2.70/1.00  ------ General Options
% 2.70/1.00  
% 2.70/1.00  --fof                                   false
% 2.70/1.00  --time_out_real                         305.
% 2.70/1.00  --time_out_virtual                      -1.
% 2.70/1.00  --symbol_type_check                     false
% 2.70/1.00  --clausify_out                          false
% 2.70/1.00  --sig_cnt_out                           false
% 2.70/1.00  --trig_cnt_out                          false
% 2.70/1.00  --trig_cnt_out_tolerance                1.
% 2.70/1.00  --trig_cnt_out_sk_spl                   false
% 2.70/1.00  --abstr_cl_out                          false
% 2.70/1.00  
% 2.70/1.00  ------ Global Options
% 2.70/1.00  
% 2.70/1.00  --schedule                              default
% 2.70/1.00  --add_important_lit                     false
% 2.70/1.00  --prop_solver_per_cl                    1000
% 2.70/1.00  --min_unsat_core                        false
% 2.70/1.00  --soft_assumptions                      false
% 2.70/1.00  --soft_lemma_size                       3
% 2.70/1.00  --prop_impl_unit_size                   0
% 2.70/1.00  --prop_impl_unit                        []
% 2.70/1.00  --share_sel_clauses                     true
% 2.70/1.00  --reset_solvers                         false
% 2.70/1.00  --bc_imp_inh                            [conj_cone]
% 2.70/1.00  --conj_cone_tolerance                   3.
% 2.70/1.00  --extra_neg_conj                        none
% 2.70/1.00  --large_theory_mode                     true
% 2.70/1.00  --prolific_symb_bound                   200
% 2.70/1.00  --lt_threshold                          2000
% 2.70/1.00  --clause_weak_htbl                      true
% 2.70/1.00  --gc_record_bc_elim                     false
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing Options
% 2.70/1.00  
% 2.70/1.00  --preprocessing_flag                    true
% 2.70/1.00  --time_out_prep_mult                    0.1
% 2.70/1.00  --splitting_mode                        input
% 2.70/1.00  --splitting_grd                         true
% 2.70/1.00  --splitting_cvd                         false
% 2.70/1.00  --splitting_cvd_svl                     false
% 2.70/1.00  --splitting_nvd                         32
% 2.70/1.00  --sub_typing                            true
% 2.70/1.00  --prep_gs_sim                           true
% 2.70/1.00  --prep_unflatten                        true
% 2.70/1.00  --prep_res_sim                          true
% 2.70/1.00  --prep_upred                            true
% 2.70/1.00  --prep_sem_filter                       exhaustive
% 2.70/1.00  --prep_sem_filter_out                   false
% 2.70/1.00  --pred_elim                             true
% 2.70/1.00  --res_sim_input                         true
% 2.70/1.00  --eq_ax_congr_red                       true
% 2.70/1.00  --pure_diseq_elim                       true
% 2.70/1.00  --brand_transform                       false
% 2.70/1.00  --non_eq_to_eq                          false
% 2.70/1.00  --prep_def_merge                        true
% 2.70/1.00  --prep_def_merge_prop_impl              false
% 2.70/1.00  --prep_def_merge_mbd                    true
% 2.70/1.00  --prep_def_merge_tr_red                 false
% 2.70/1.00  --prep_def_merge_tr_cl                  false
% 2.70/1.00  --smt_preprocessing                     true
% 2.70/1.00  --smt_ac_axioms                         fast
% 2.70/1.00  --preprocessed_out                      false
% 2.70/1.00  --preprocessed_stats                    false
% 2.70/1.00  
% 2.70/1.00  ------ Abstraction refinement Options
% 2.70/1.00  
% 2.70/1.00  --abstr_ref                             []
% 2.70/1.00  --abstr_ref_prep                        false
% 2.70/1.00  --abstr_ref_until_sat                   false
% 2.70/1.00  --abstr_ref_sig_restrict                funpre
% 2.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.00  --abstr_ref_under                       []
% 2.70/1.00  
% 2.70/1.00  ------ SAT Options
% 2.70/1.00  
% 2.70/1.00  --sat_mode                              false
% 2.70/1.00  --sat_fm_restart_options                ""
% 2.70/1.00  --sat_gr_def                            false
% 2.70/1.00  --sat_epr_types                         true
% 2.70/1.00  --sat_non_cyclic_types                  false
% 2.70/1.00  --sat_finite_models                     false
% 2.70/1.00  --sat_fm_lemmas                         false
% 2.70/1.00  --sat_fm_prep                           false
% 2.70/1.00  --sat_fm_uc_incr                        true
% 2.70/1.00  --sat_out_model                         small
% 2.70/1.00  --sat_out_clauses                       false
% 2.70/1.00  
% 2.70/1.00  ------ QBF Options
% 2.70/1.00  
% 2.70/1.00  --qbf_mode                              false
% 2.70/1.00  --qbf_elim_univ                         false
% 2.70/1.00  --qbf_dom_inst                          none
% 2.70/1.00  --qbf_dom_pre_inst                      false
% 2.70/1.00  --qbf_sk_in                             false
% 2.70/1.00  --qbf_pred_elim                         true
% 2.70/1.00  --qbf_split                             512
% 2.70/1.00  
% 2.70/1.00  ------ BMC1 Options
% 2.70/1.00  
% 2.70/1.00  --bmc1_incremental                      false
% 2.70/1.00  --bmc1_axioms                           reachable_all
% 2.70/1.00  --bmc1_min_bound                        0
% 2.70/1.00  --bmc1_max_bound                        -1
% 2.70/1.00  --bmc1_max_bound_default                -1
% 2.70/1.00  --bmc1_symbol_reachability              true
% 2.70/1.00  --bmc1_property_lemmas                  false
% 2.70/1.00  --bmc1_k_induction                      false
% 2.70/1.00  --bmc1_non_equiv_states                 false
% 2.70/1.00  --bmc1_deadlock                         false
% 2.70/1.00  --bmc1_ucm                              false
% 2.70/1.00  --bmc1_add_unsat_core                   none
% 2.70/1.00  --bmc1_unsat_core_children              false
% 2.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.00  --bmc1_out_stat                         full
% 2.70/1.00  --bmc1_ground_init                      false
% 2.70/1.00  --bmc1_pre_inst_next_state              false
% 2.70/1.00  --bmc1_pre_inst_state                   false
% 2.70/1.00  --bmc1_pre_inst_reach_state             false
% 2.70/1.00  --bmc1_out_unsat_core                   false
% 2.70/1.00  --bmc1_aig_witness_out                  false
% 2.70/1.00  --bmc1_verbose                          false
% 2.70/1.00  --bmc1_dump_clauses_tptp                false
% 2.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.00  --bmc1_dump_file                        -
% 2.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.00  --bmc1_ucm_extend_mode                  1
% 2.70/1.00  --bmc1_ucm_init_mode                    2
% 2.70/1.00  --bmc1_ucm_cone_mode                    none
% 2.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.00  --bmc1_ucm_relax_model                  4
% 2.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.00  --bmc1_ucm_layered_model                none
% 2.70/1.00  --bmc1_ucm_max_lemma_size               10
% 2.70/1.00  
% 2.70/1.00  ------ AIG Options
% 2.70/1.00  
% 2.70/1.00  --aig_mode                              false
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation Options
% 2.70/1.00  
% 2.70/1.00  --instantiation_flag                    true
% 2.70/1.00  --inst_sos_flag                         false
% 2.70/1.00  --inst_sos_phase                        true
% 2.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel_side                     none
% 2.70/1.00  --inst_solver_per_active                1400
% 2.70/1.00  --inst_solver_calls_frac                1.
% 2.70/1.00  --inst_passive_queue_type               priority_queues
% 2.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.00  --inst_passive_queues_freq              [25;2]
% 2.70/1.00  --inst_dismatching                      true
% 2.70/1.00  --inst_eager_unprocessed_to_passive     true
% 2.70/1.00  --inst_prop_sim_given                   true
% 2.70/1.00  --inst_prop_sim_new                     false
% 2.70/1.00  --inst_subs_new                         false
% 2.70/1.00  --inst_eq_res_simp                      false
% 2.70/1.00  --inst_subs_given                       false
% 2.70/1.00  --inst_orphan_elimination               true
% 2.70/1.00  --inst_learning_loop_flag               true
% 2.70/1.00  --inst_learning_start                   3000
% 2.70/1.00  --inst_learning_factor                  2
% 2.70/1.00  --inst_start_prop_sim_after_learn       3
% 2.70/1.00  --inst_sel_renew                        solver
% 2.70/1.00  --inst_lit_activity_flag                true
% 2.70/1.00  --inst_restr_to_given                   false
% 2.70/1.00  --inst_activity_threshold               500
% 2.70/1.00  --inst_out_proof                        true
% 2.70/1.00  
% 2.70/1.00  ------ Resolution Options
% 2.70/1.00  
% 2.70/1.00  --resolution_flag                       false
% 2.70/1.00  --res_lit_sel                           adaptive
% 2.70/1.00  --res_lit_sel_side                      none
% 2.70/1.00  --res_ordering                          kbo
% 2.70/1.00  --res_to_prop_solver                    active
% 2.70/1.00  --res_prop_simpl_new                    false
% 2.70/1.00  --res_prop_simpl_given                  true
% 2.70/1.00  --res_passive_queue_type                priority_queues
% 2.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.00  --res_passive_queues_freq               [15;5]
% 2.70/1.00  --res_forward_subs                      full
% 2.70/1.00  --res_backward_subs                     full
% 2.70/1.00  --res_forward_subs_resolution           true
% 2.70/1.00  --res_backward_subs_resolution          true
% 2.70/1.00  --res_orphan_elimination                true
% 2.70/1.00  --res_time_limit                        2.
% 2.70/1.00  --res_out_proof                         true
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Options
% 2.70/1.00  
% 2.70/1.00  --superposition_flag                    true
% 2.70/1.00  --sup_passive_queue_type                priority_queues
% 2.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.00  --demod_completeness_check              fast
% 2.70/1.00  --demod_use_ground                      true
% 2.70/1.00  --sup_to_prop_solver                    passive
% 2.70/1.00  --sup_prop_simpl_new                    true
% 2.70/1.00  --sup_prop_simpl_given                  true
% 2.70/1.00  --sup_fun_splitting                     false
% 2.70/1.00  --sup_smt_interval                      50000
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Simplification Setup
% 2.70/1.00  
% 2.70/1.00  --sup_indices_passive                   []
% 2.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_full_bw                           [BwDemod]
% 2.70/1.00  --sup_immed_triv                        [TrivRules]
% 2.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_immed_bw_main                     []
% 2.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  
% 2.70/1.00  ------ Combination Options
% 2.70/1.00  
% 2.70/1.00  --comb_res_mult                         3
% 2.70/1.00  --comb_sup_mult                         2
% 2.70/1.00  --comb_inst_mult                        10
% 2.70/1.00  
% 2.70/1.00  ------ Debug Options
% 2.70/1.00  
% 2.70/1.00  --dbg_backtrace                         false
% 2.70/1.00  --dbg_dump_prop_clauses                 false
% 2.70/1.00  --dbg_dump_prop_clauses_file            -
% 2.70/1.00  --dbg_out_stat                          false
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  ------ Proving...
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  % SZS status Theorem for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  fof(f15,conjecture,(
% 2.70/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f16,negated_conjecture,(
% 2.70/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.70/1.00    inference(negated_conjecture,[],[f15])).
% 2.70/1.00  
% 2.70/1.00  fof(f33,plain,(
% 2.70/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.70/1.00    inference(ennf_transformation,[],[f16])).
% 2.70/1.00  
% 2.70/1.00  fof(f34,plain,(
% 2.70/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.70/1.00    inference(flattening,[],[f33])).
% 2.70/1.00  
% 2.70/1.00  fof(f39,plain,(
% 2.70/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.70/1.00    introduced(choice_axiom,[])).
% 2.70/1.00  
% 2.70/1.00  fof(f40,plain,(
% 2.70/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f39])).
% 2.70/1.00  
% 2.70/1.00  fof(f65,plain,(
% 2.70/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.70/1.00    inference(cnf_transformation,[],[f40])).
% 2.70/1.00  
% 2.70/1.00  fof(f12,axiom,(
% 2.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f29,plain,(
% 2.70/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/1.00    inference(ennf_transformation,[],[f12])).
% 2.70/1.00  
% 2.70/1.00  fof(f58,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f67,plain,(
% 2.70/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.70/1.00    inference(cnf_transformation,[],[f40])).
% 2.70/1.00  
% 2.70/1.00  fof(f2,axiom,(
% 2.70/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f37,plain,(
% 2.70/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.70/1.00    inference(nnf_transformation,[],[f2])).
% 2.70/1.00  
% 2.70/1.00  fof(f44,plain,(
% 2.70/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f37])).
% 2.70/1.00  
% 2.70/1.00  fof(f3,axiom,(
% 2.70/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f17,plain,(
% 2.70/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.70/1.00    inference(ennf_transformation,[],[f3])).
% 2.70/1.00  
% 2.70/1.00  fof(f46,plain,(
% 2.70/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f17])).
% 2.70/1.00  
% 2.70/1.00  fof(f45,plain,(
% 2.70/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f37])).
% 2.70/1.00  
% 2.70/1.00  fof(f5,axiom,(
% 2.70/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f49,plain,(
% 2.70/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f5])).
% 2.70/1.00  
% 2.70/1.00  fof(f10,axiom,(
% 2.70/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f26,plain,(
% 2.70/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.70/1.00    inference(ennf_transformation,[],[f10])).
% 2.70/1.00  
% 2.70/1.00  fof(f27,plain,(
% 2.70/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.70/1.00    inference(flattening,[],[f26])).
% 2.70/1.00  
% 2.70/1.00  fof(f55,plain,(
% 2.70/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f27])).
% 2.70/1.00  
% 2.70/1.00  fof(f66,plain,(
% 2.70/1.00    v2_funct_1(sK2)),
% 2.70/1.00    inference(cnf_transformation,[],[f40])).
% 2.70/1.00  
% 2.70/1.00  fof(f63,plain,(
% 2.70/1.00    v1_funct_1(sK2)),
% 2.70/1.00    inference(cnf_transformation,[],[f40])).
% 2.70/1.00  
% 2.70/1.00  fof(f14,axiom,(
% 2.70/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f31,plain,(
% 2.70/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.70/1.00    inference(ennf_transformation,[],[f14])).
% 2.70/1.00  
% 2.70/1.00  fof(f32,plain,(
% 2.70/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(flattening,[],[f31])).
% 2.70/1.00  
% 2.70/1.00  fof(f62,plain,(
% 2.70/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f32])).
% 2.70/1.00  
% 2.70/1.00  fof(f56,plain,(
% 2.70/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f27])).
% 2.70/1.00  
% 2.70/1.00  fof(f8,axiom,(
% 2.70/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f22,plain,(
% 2.70/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.70/1.00    inference(ennf_transformation,[],[f8])).
% 2.70/1.00  
% 2.70/1.00  fof(f23,plain,(
% 2.70/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.70/1.00    inference(flattening,[],[f22])).
% 2.70/1.00  
% 2.70/1.00  fof(f52,plain,(
% 2.70/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f23])).
% 2.70/1.00  
% 2.70/1.00  fof(f53,plain,(
% 2.70/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f23])).
% 2.70/1.00  
% 2.70/1.00  fof(f1,axiom,(
% 2.70/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f35,plain,(
% 2.70/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/1.00    inference(nnf_transformation,[],[f1])).
% 2.70/1.00  
% 2.70/1.00  fof(f36,plain,(
% 2.70/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/1.00    inference(flattening,[],[f35])).
% 2.70/1.00  
% 2.70/1.00  fof(f41,plain,(
% 2.70/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.70/1.00    inference(cnf_transformation,[],[f36])).
% 2.70/1.00  
% 2.70/1.00  fof(f70,plain,(
% 2.70/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.70/1.00    inference(equality_resolution,[],[f41])).
% 2.70/1.00  
% 2.70/1.00  fof(f4,axiom,(
% 2.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f18,plain,(
% 2.70/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(ennf_transformation,[],[f4])).
% 2.70/1.00  
% 2.70/1.00  fof(f38,plain,(
% 2.70/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(nnf_transformation,[],[f18])).
% 2.70/1.00  
% 2.70/1.00  fof(f48,plain,(
% 2.70/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f38])).
% 2.70/1.00  
% 2.70/1.00  fof(f7,axiom,(
% 2.70/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f20,plain,(
% 2.70/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.70/1.00    inference(ennf_transformation,[],[f7])).
% 2.70/1.00  
% 2.70/1.00  fof(f21,plain,(
% 2.70/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(flattening,[],[f20])).
% 2.70/1.00  
% 2.70/1.00  fof(f51,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f21])).
% 2.70/1.00  
% 2.70/1.00  fof(f6,axiom,(
% 2.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f19,plain,(
% 2.70/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(ennf_transformation,[],[f6])).
% 2.70/1.00  
% 2.70/1.00  fof(f50,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f19])).
% 2.70/1.00  
% 2.70/1.00  fof(f9,axiom,(
% 2.70/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f24,plain,(
% 2.70/1.00    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.70/1.00    inference(ennf_transformation,[],[f9])).
% 2.70/1.00  
% 2.70/1.00  fof(f25,plain,(
% 2.70/1.00    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.70/1.00    inference(flattening,[],[f24])).
% 2.70/1.00  
% 2.70/1.00  fof(f54,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f25])).
% 2.70/1.00  
% 2.70/1.00  fof(f13,axiom,(
% 2.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f30,plain,(
% 2.70/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/1.00    inference(ennf_transformation,[],[f13])).
% 2.70/1.00  
% 2.70/1.00  fof(f59,plain,(
% 2.70/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f30])).
% 2.70/1.00  
% 2.70/1.00  fof(f11,axiom,(
% 2.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f28,plain,(
% 2.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/1.00    inference(ennf_transformation,[],[f11])).
% 2.70/1.00  
% 2.70/1.00  fof(f57,plain,(
% 2.70/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f28])).
% 2.70/1.00  
% 2.70/1.00  fof(f61,plain,(
% 2.70/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f32])).
% 2.70/1.00  
% 2.70/1.00  fof(f68,plain,(
% 2.70/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.70/1.00    inference(cnf_transformation,[],[f40])).
% 2.70/1.00  
% 2.70/1.00  cnf(c_25,negated_conjecture,
% 2.70/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1185,plain,
% 2.70/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_17,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1188,plain,
% 2.70/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2095,plain,
% 2.70/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1185,c_1188]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_23,negated_conjecture,
% 2.70/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.70/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2097,plain,
% 2.70/1.00      ( k2_relat_1(sK2) = sK1 ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_2095,c_23]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1194,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.70/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1630,plain,
% 2.70/1.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1185,c_1194]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_5,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/1.00      | ~ v1_relat_1(X1)
% 2.70/1.00      | v1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_206,plain,
% 2.70/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.70/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_207,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/1.00      inference(renaming,[status(thm)],[c_206]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_249,plain,
% 2.70/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.70/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_207]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1183,plain,
% 2.70/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.70/1.00      | v1_relat_1(X1) != iProver_top
% 2.70/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1852,plain,
% 2.70/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.70/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1630,c_1183]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_8,plain,
% 2.70/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1193,plain,
% 2.70/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1861,plain,
% 2.70/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.70/1.00      inference(forward_subsumption_resolution,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_1852,c_1193]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_15,plain,
% 2.70/1.00      ( ~ v2_funct_1(X0)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_24,negated_conjecture,
% 2.70/1.00      ( v2_funct_1(sK2) ),
% 2.70/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_405,plain,
% 2.70/1.00      ( ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.70/1.00      | sK2 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_406,plain,
% 2.70/1.00      ( ~ v1_funct_1(sK2)
% 2.70/1.00      | ~ v1_relat_1(sK2)
% 2.70/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_27,negated_conjecture,
% 2.70/1.00      ( v1_funct_1(sK2) ),
% 2.70/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_408,plain,
% 2.70/1.00      ( ~ v1_relat_1(sK2)
% 2.70/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_406,c_27]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1179,plain,
% 2.70/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.70/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1865,plain,
% 2.70/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1861,c_1179]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2168,plain,
% 2.70/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.70/1.00      inference(demodulation,[status(thm)],[c_2097,c_1865]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_19,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.70/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1186,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.70/1.00      | v1_funct_1(X0) != iProver_top
% 2.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2242,plain,
% 2.70/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2168,c_1186]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_14,plain,
% 2.70/1.00      ( ~ v2_funct_1(X0)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_419,plain,
% 2.70/1.00      ( ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.70/1.00      | sK2 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_420,plain,
% 2.70/1.00      ( ~ v1_funct_1(sK2)
% 2.70/1.00      | ~ v1_relat_1(sK2)
% 2.70/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_419]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_53,plain,
% 2.70/1.00      ( ~ v2_funct_1(sK2)
% 2.70/1.00      | ~ v1_funct_1(sK2)
% 2.70/1.00      | ~ v1_relat_1(sK2)
% 2.70/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_422,plain,
% 2.70/1.00      ( ~ v1_relat_1(sK2)
% 2.70/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_420,c_27,c_24,c_53]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1178,plain,
% 2.70/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.70/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1866,plain,
% 2.70/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1861,c_1178]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2243,plain,
% 2.70/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.70/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_2242,c_1866]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_28,plain,
% 2.70/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_12,plain,
% 2.70/1.00      ( ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_58,plain,
% 2.70/1.00      ( v1_funct_1(X0) != iProver_top
% 2.70/1.00      | v1_relat_1(X0) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_60,plain,
% 2.70/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.70/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_58]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_11,plain,
% 2.70/1.00      ( ~ v1_funct_1(X0)
% 2.70/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.70/1.00      | ~ v1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_61,plain,
% 2.70/1.00      ( v1_funct_1(X0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_63,plain,
% 2.70/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.70/1.00      | v1_funct_1(sK2) != iProver_top
% 2.70/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2409,plain,
% 2.70/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.70/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_2243,c_28,c_60,c_63,c_1861]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2417,plain,
% 2.70/1.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,X0)) = iProver_top
% 2.70/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2409,c_1194]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3388,plain,
% 2.70/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_zfmisc_1(sK1,X0)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2417,c_1183]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3891,plain,
% 2.70/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_3388,c_28,c_60,c_1861]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2,plain,
% 2.70/1.00      ( r1_tarski(X0,X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1196,plain,
% 2.70/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_6,plain,
% 2.70/1.00      ( v4_relat_1(X0,X1)
% 2.70/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.70/1.00      | ~ v1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_10,plain,
% 2.70/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.70/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_386,plain,
% 2.70/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.70/1.00      inference(resolution,[status(thm)],[c_6,c_10]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1180,plain,
% 2.70/1.00      ( k7_relat_1(X0,X1) = X0
% 2.70/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4440,plain,
% 2.70/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1196,c_1180]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4579,plain,
% 2.70/1.00      ( k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_3891,c_4440]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4586,plain,
% 2.70/1.00      ( k7_relat_1(k2_funct_1(sK2),sK1) = k2_funct_1(sK2) ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_4579,c_2168]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_9,plain,
% 2.70/1.00      ( ~ v1_relat_1(X0)
% 2.70/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1192,plain,
% 2.70/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3896,plain,
% 2.70/1.00      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_3891,c_1192]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_13,plain,
% 2.70/1.00      ( ~ v2_funct_1(X0)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_433,plain,
% 2.70/1.00      ( ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.70/1.00      | sK2 != X0 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_434,plain,
% 2.70/1.00      ( ~ v1_funct_1(sK2)
% 2.70/1.00      | ~ v1_relat_1(sK2)
% 2.70/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_433]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_438,plain,
% 2.70/1.00      ( ~ v1_relat_1(sK2)
% 2.70/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_434,c_27]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1177,plain,
% 2.70/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 2.70/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1864,plain,
% 2.70/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1861,c_1177]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3897,plain,
% 2.70/1.00      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_3896,c_1864]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4711,plain,
% 2.70/1.00      ( k10_relat_1(sK2,sK1) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_4586,c_3897]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4712,plain,
% 2.70/1.00      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_4711,c_1866]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_18,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.70/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1187,plain,
% 2.70/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2804,plain,
% 2.70/1.00      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1185,c_1187]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_16,plain,
% 2.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1189,plain,
% 2.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.70/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2934,plain,
% 2.70/1.00      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) = iProver_top
% 2.70/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2804,c_1189]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_30,plain,
% 2.70/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3037,plain,
% 2.70/1.00      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_2934,c_30]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3044,plain,
% 2.70/1.00      ( r1_tarski(k10_relat_1(sK2,X0),sK0) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_3037,c_1194]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4882,plain,
% 2.70/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_4712,c_3044]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_20,plain,
% 2.70/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.70/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_relat_1(X0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_22,negated_conjecture,
% 2.70/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.70/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.70/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_341,plain,
% 2.70/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.70/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.70/1.00      | ~ v1_funct_1(X0)
% 2.70/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.70/1.00      | ~ v1_relat_1(X0)
% 2.70/1.00      | k2_funct_1(sK2) != X0
% 2.70/1.00      | k1_relat_1(X0) != sK1
% 2.70/1.00      | sK0 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_342,plain,
% 2.70/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.70/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 2.70/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.70/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.70/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_341]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1182,plain,
% 2.70/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.70/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1949,plain,
% 2.70/1.00      ( k2_relat_1(sK2) != sK1
% 2.70/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.70/1.00      inference(demodulation,[status(thm)],[c_1865,c_1182]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_343,plain,
% 2.70/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.70/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 2.70/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.70/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2324,plain,
% 2.70/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.70/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_1949,c_28,c_60,c_63,c_343,c_1861,c_2168]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2328,plain,
% 2.70/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.70/1.00      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 2.70/1.00      inference(light_normalisation,[status(thm)],[c_2324,c_1866]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2419,plain,
% 2.70/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2409,c_2328]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(contradiction,plain,
% 2.70/1.00      ( $false ),
% 2.70/1.00      inference(minisat,[status(thm)],[c_4882,c_2419]) ).
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  ------                               Statistics
% 2.70/1.00  
% 2.70/1.00  ------ General
% 2.70/1.00  
% 2.70/1.00  abstr_ref_over_cycles:                  0
% 2.70/1.00  abstr_ref_under_cycles:                 0
% 2.70/1.00  gc_basic_clause_elim:                   0
% 2.70/1.00  forced_gc_time:                         0
% 2.70/1.00  parsing_time:                           0.024
% 2.70/1.00  unif_index_cands_time:                  0.
% 2.70/1.00  unif_index_add_time:                    0.
% 2.70/1.00  orderings_time:                         0.
% 2.70/1.00  out_proof_time:                         0.01
% 2.70/1.00  total_time:                             0.281
% 2.70/1.00  num_of_symbols:                         51
% 2.70/1.00  num_of_terms:                           4244
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing
% 2.70/1.00  
% 2.70/1.00  num_of_splits:                          0
% 2.70/1.00  num_of_split_atoms:                     0
% 2.70/1.00  num_of_reused_defs:                     0
% 2.70/1.00  num_eq_ax_congr_red:                    28
% 2.70/1.00  num_of_sem_filtered_clauses:            1
% 2.70/1.00  num_of_subtypes:                        0
% 2.70/1.00  monotx_restored_types:                  0
% 2.70/1.00  sat_num_of_epr_types:                   0
% 2.70/1.00  sat_num_of_non_cyclic_types:            0
% 2.70/1.00  sat_guarded_non_collapsed_types:        0
% 2.70/1.00  num_pure_diseq_elim:                    0
% 2.70/1.00  simp_replaced_by:                       0
% 2.70/1.00  res_preprocessed:                       121
% 2.70/1.00  prep_upred:                             0
% 2.70/1.00  prep_unflattend:                        5
% 2.70/1.00  smt_new_axioms:                         0
% 2.70/1.00  pred_elim_cands:                        4
% 2.70/1.00  pred_elim:                              3
% 2.70/1.00  pred_elim_cl:                           4
% 2.70/1.00  pred_elim_cycles:                       5
% 2.70/1.00  merged_defs:                            8
% 2.70/1.00  merged_defs_ncl:                        0
% 2.70/1.00  bin_hyper_res:                          9
% 2.70/1.00  prep_cycles:                            4
% 2.70/1.00  pred_elim_time:                         0.039
% 2.70/1.00  splitting_time:                         0.
% 2.70/1.00  sem_filter_time:                        0.
% 2.70/1.00  monotx_time:                            0.001
% 2.70/1.00  subtype_inf_time:                       0.
% 2.70/1.00  
% 2.70/1.00  ------ Problem properties
% 2.70/1.00  
% 2.70/1.00  clauses:                                22
% 2.70/1.00  conjectures:                            3
% 2.70/1.00  epr:                                    4
% 2.70/1.00  horn:                                   22
% 2.70/1.00  ground:                                 7
% 2.70/1.00  unary:                                  5
% 2.70/1.00  binary:                                 9
% 2.70/1.00  lits:                                   51
% 2.70/1.00  lits_eq:                                12
% 2.70/1.00  fd_pure:                                0
% 2.70/1.00  fd_pseudo:                              0
% 2.70/1.00  fd_cond:                                0
% 2.70/1.00  fd_pseudo_cond:                         1
% 2.70/1.00  ac_symbols:                             0
% 2.70/1.00  
% 2.70/1.00  ------ Propositional Solver
% 2.70/1.00  
% 2.70/1.00  prop_solver_calls:                      28
% 2.70/1.00  prop_fast_solver_calls:                 770
% 2.70/1.00  smt_solver_calls:                       0
% 2.70/1.00  smt_fast_solver_calls:                  0
% 2.70/1.00  prop_num_of_clauses:                    1590
% 2.70/1.00  prop_preprocess_simplified:             5509
% 2.70/1.00  prop_fo_subsumed:                       16
% 2.70/1.00  prop_solver_time:                       0.
% 2.70/1.00  smt_solver_time:                        0.
% 2.70/1.00  smt_fast_solver_time:                   0.
% 2.70/1.00  prop_fast_solver_time:                  0.
% 2.70/1.00  prop_unsat_core_time:                   0.
% 2.70/1.00  
% 2.70/1.00  ------ QBF
% 2.70/1.00  
% 2.70/1.00  qbf_q_res:                              0
% 2.70/1.00  qbf_num_tautologies:                    0
% 2.70/1.00  qbf_prep_cycles:                        0
% 2.70/1.00  
% 2.70/1.00  ------ BMC1
% 2.70/1.00  
% 2.70/1.00  bmc1_current_bound:                     -1
% 2.70/1.00  bmc1_last_solved_bound:                 -1
% 2.70/1.00  bmc1_unsat_core_size:                   -1
% 2.70/1.00  bmc1_unsat_core_parents_size:           -1
% 2.70/1.00  bmc1_merge_next_fun:                    0
% 2.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation
% 2.70/1.00  
% 2.70/1.00  inst_num_of_clauses:                    482
% 2.70/1.00  inst_num_in_passive:                    4
% 2.70/1.01  inst_num_in_active:                     308
% 2.70/1.01  inst_num_in_unprocessed:                171
% 2.70/1.01  inst_num_of_loops:                      330
% 2.70/1.01  inst_num_of_learning_restarts:          0
% 2.70/1.01  inst_num_moves_active_passive:          19
% 2.70/1.01  inst_lit_activity:                      0
% 2.70/1.01  inst_lit_activity_moves:                0
% 2.70/1.01  inst_num_tautologies:                   0
% 2.70/1.01  inst_num_prop_implied:                  0
% 2.70/1.01  inst_num_existing_simplified:           0
% 2.70/1.01  inst_num_eq_res_simplified:             0
% 2.70/1.01  inst_num_child_elim:                    0
% 2.70/1.01  inst_num_of_dismatching_blockings:      249
% 2.70/1.01  inst_num_of_non_proper_insts:           854
% 2.70/1.01  inst_num_of_duplicates:                 0
% 2.70/1.01  inst_inst_num_from_inst_to_res:         0
% 2.70/1.01  inst_dismatching_checking_time:         0.
% 2.70/1.01  
% 2.70/1.01  ------ Resolution
% 2.70/1.01  
% 2.70/1.01  res_num_of_clauses:                     0
% 2.70/1.01  res_num_in_passive:                     0
% 2.70/1.01  res_num_in_active:                      0
% 2.70/1.01  res_num_of_loops:                       125
% 2.70/1.01  res_forward_subset_subsumed:            109
% 2.70/1.01  res_backward_subset_subsumed:           2
% 2.70/1.01  res_forward_subsumed:                   0
% 2.70/1.01  res_backward_subsumed:                  0
% 2.70/1.01  res_forward_subsumption_resolution:     0
% 2.70/1.01  res_backward_subsumption_resolution:    0
% 2.70/1.01  res_clause_to_clause_subsumption:       288
% 2.70/1.01  res_orphan_elimination:                 0
% 2.70/1.01  res_tautology_del:                      85
% 2.70/1.01  res_num_eq_res_simplified:              0
% 2.70/1.01  res_num_sel_changes:                    0
% 2.70/1.01  res_moves_from_active_to_pass:          0
% 2.70/1.01  
% 2.70/1.01  ------ Superposition
% 2.70/1.01  
% 2.70/1.01  sup_time_total:                         0.
% 2.70/1.01  sup_time_generating:                    0.
% 2.70/1.01  sup_time_sim_full:                      0.
% 2.70/1.01  sup_time_sim_immed:                     0.
% 2.70/1.01  
% 2.70/1.01  sup_num_of_clauses:                     86
% 2.70/1.01  sup_num_in_active:                      60
% 2.70/1.01  sup_num_in_passive:                     26
% 2.70/1.01  sup_num_of_loops:                       64
% 2.70/1.01  sup_fw_superposition:                   51
% 2.70/1.01  sup_bw_superposition:                   34
% 2.70/1.01  sup_immediate_simplified:               10
% 2.70/1.01  sup_given_eliminated:                   0
% 2.70/1.01  comparisons_done:                       0
% 2.70/1.01  comparisons_avoided:                    0
% 2.70/1.01  
% 2.70/1.01  ------ Simplifications
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  sim_fw_subset_subsumed:                 2
% 2.70/1.01  sim_bw_subset_subsumed:                 3
% 2.70/1.01  sim_fw_subsumed:                        0
% 2.70/1.01  sim_bw_subsumed:                        0
% 2.70/1.01  sim_fw_subsumption_res:                 1
% 2.70/1.01  sim_bw_subsumption_res:                 0
% 2.70/1.01  sim_tautology_del:                      3
% 2.70/1.01  sim_eq_tautology_del:                   1
% 2.70/1.01  sim_eq_res_simp:                        0
% 2.70/1.01  sim_fw_demodulated:                     1
% 2.70/1.01  sim_bw_demodulated:                     2
% 2.70/1.01  sim_light_normalised:                   9
% 2.70/1.01  sim_joinable_taut:                      0
% 2.70/1.01  sim_joinable_simp:                      0
% 2.70/1.01  sim_ac_normalised:                      0
% 2.70/1.01  sim_smt_subsumption:                    0
% 2.70/1.01  
%------------------------------------------------------------------------------
