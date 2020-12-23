%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:36 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 806 expanded)
%              Number of clauses        :  111 ( 277 expanded)
%              Number of leaves         :   18 ( 157 expanded)
%              Depth                    :   21
%              Number of atoms          :  494 (3684 expanded)
%              Number of equality atoms :  212 (1138 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_369,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_370,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_328,plain,
    ( ~ v1_relat_1(sK2)
    | k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_462,plain,
    ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[status(thm)],[c_370,c_328])).

cnf(c_579,plain,
    ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_462])).

cnf(c_850,plain,
    ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_372,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_582,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_963,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1410,plain,
    ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_328,c_372,c_963])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_360,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_361,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_974,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_361])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_270,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_24,c_21])).

cnf(c_975,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_974,c_270])).

cnf(c_1413,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1410,c_975])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_342,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_343,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_991,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_343])).

cnf(c_19,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1012,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_991,c_19])).

cnf(c_1013,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1012,c_991])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_351,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_352,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_995,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_352])).

cnf(c_1224,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1013,c_995])).

cnf(c_1416,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1413,c_1224])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_499,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_370])).

cnf(c_500,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_573,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_500])).

cnf(c_612,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_277,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_279,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_24,c_21])).

cnf(c_302,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_279])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_307,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_24])).

cnf(c_470,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[status(thm)],[c_370,c_307])).

cnf(c_578,plain,
    ( sP3_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_470])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1002,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1037,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1038,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_577,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_470])).

cnf(c_1149,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ sP3_iProver_split
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_584,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1032,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(sK2))
    | X2 != X0
    | k1_relat_1(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_1164,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_relat_1(sK2))
    | k1_relat_1(sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1319,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_relat_1(sK2))
    | k1_relat_1(sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1321,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ r1_tarski(sK1,sK0)
    | k1_relat_1(sK2) != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2181,plain,
    ( k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1416,c_20,c_612,c_578,c_963,c_975,c_1037,c_1038,c_1149,c_1321])).

cnf(c_852,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_853,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1060,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_852,c_853])).

cnf(c_854,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_484,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_370])).

cnf(c_485,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_575,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | k7_relat_1(sK2,X0) = sK2
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_485])).

cnf(c_844,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_611,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_613,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_576,plain,
    ( sP2_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_485])).

cnf(c_617,plain,
    ( sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_618,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1418,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_844,c_613,c_617,c_618,c_963])).

cnf(c_1419,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1418])).

cnf(c_1424,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1419,c_975])).

cnf(c_1430,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_854,c_1424])).

cnf(c_572,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_500])).

cnf(c_842,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_574,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_500])).

cnf(c_1355,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_574,c_612,c_572,c_963])).

cnf(c_1522,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1430,c_1355])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_287,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_288,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_24,c_21])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_381,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_382,plain,
    ( v5_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_405,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_382])).

cnf(c_406,plain,
    ( ~ v2_funct_2(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_418,plain,
    ( ~ v2_funct_2(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_406,c_370])).

cnf(c_449,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = X1
    | sK2 != sK2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_418])).

cnf(c_450,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_423,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1014,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_24,c_21,c_288,c_423,c_963])).

cnf(c_1523,plain,
    ( k9_relat_1(sK2,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1522,c_1014])).

cnf(c_2183,plain,
    ( sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_2181,c_1060,c_1523])).

cnf(c_2184,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:13:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.93/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/0.98  
% 1.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.98  
% 1.93/0.98  ------  iProver source info
% 1.93/0.98  
% 1.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.98  git: non_committed_changes: false
% 1.93/0.98  git: last_make_outside_of_git: false
% 1.93/0.98  
% 1.93/0.98  ------ 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options
% 1.93/0.98  
% 1.93/0.98  --out_options                           all
% 1.93/0.98  --tptp_safe_out                         true
% 1.93/0.98  --problem_path                          ""
% 1.93/0.98  --include_path                          ""
% 1.93/0.98  --clausifier                            res/vclausify_rel
% 1.93/0.98  --clausifier_options                    --mode clausify
% 1.93/0.98  --stdin                                 false
% 1.93/0.98  --stats_out                             all
% 1.93/0.98  
% 1.93/0.98  ------ General Options
% 1.93/0.98  
% 1.93/0.98  --fof                                   false
% 1.93/0.98  --time_out_real                         305.
% 1.93/0.98  --time_out_virtual                      -1.
% 1.93/0.98  --symbol_type_check                     false
% 1.93/0.98  --clausify_out                          false
% 1.93/0.98  --sig_cnt_out                           false
% 1.93/0.98  --trig_cnt_out                          false
% 1.93/0.98  --trig_cnt_out_tolerance                1.
% 1.93/0.98  --trig_cnt_out_sk_spl                   false
% 1.93/0.98  --abstr_cl_out                          false
% 1.93/0.98  
% 1.93/0.98  ------ Global Options
% 1.93/0.98  
% 1.93/0.98  --schedule                              default
% 1.93/0.98  --add_important_lit                     false
% 1.93/0.98  --prop_solver_per_cl                    1000
% 1.93/0.98  --min_unsat_core                        false
% 1.93/0.98  --soft_assumptions                      false
% 1.93/0.98  --soft_lemma_size                       3
% 1.93/0.98  --prop_impl_unit_size                   0
% 1.93/0.98  --prop_impl_unit                        []
% 1.93/0.98  --share_sel_clauses                     true
% 1.93/0.98  --reset_solvers                         false
% 1.93/0.98  --bc_imp_inh                            [conj_cone]
% 1.93/0.98  --conj_cone_tolerance                   3.
% 1.93/0.98  --extra_neg_conj                        none
% 1.93/0.98  --large_theory_mode                     true
% 1.93/0.98  --prolific_symb_bound                   200
% 1.93/0.98  --lt_threshold                          2000
% 1.93/0.98  --clause_weak_htbl                      true
% 1.93/0.98  --gc_record_bc_elim                     false
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing Options
% 1.93/0.98  
% 1.93/0.98  --preprocessing_flag                    true
% 1.93/0.98  --time_out_prep_mult                    0.1
% 1.93/0.98  --splitting_mode                        input
% 1.93/0.98  --splitting_grd                         true
% 1.93/0.98  --splitting_cvd                         false
% 1.93/0.98  --splitting_cvd_svl                     false
% 1.93/0.98  --splitting_nvd                         32
% 1.93/0.98  --sub_typing                            true
% 1.93/0.98  --prep_gs_sim                           true
% 1.93/0.98  --prep_unflatten                        true
% 1.93/0.98  --prep_res_sim                          true
% 1.93/0.98  --prep_upred                            true
% 1.93/0.98  --prep_sem_filter                       exhaustive
% 1.93/0.98  --prep_sem_filter_out                   false
% 1.93/0.98  --pred_elim                             true
% 1.93/0.98  --res_sim_input                         true
% 1.93/0.98  --eq_ax_congr_red                       true
% 1.93/0.98  --pure_diseq_elim                       true
% 1.93/0.98  --brand_transform                       false
% 1.93/0.98  --non_eq_to_eq                          false
% 1.93/0.98  --prep_def_merge                        true
% 1.93/0.98  --prep_def_merge_prop_impl              false
% 1.93/0.98  --prep_def_merge_mbd                    true
% 1.93/0.98  --prep_def_merge_tr_red                 false
% 1.93/0.98  --prep_def_merge_tr_cl                  false
% 1.93/0.98  --smt_preprocessing                     true
% 1.93/0.98  --smt_ac_axioms                         fast
% 1.93/0.98  --preprocessed_out                      false
% 1.93/0.98  --preprocessed_stats                    false
% 1.93/0.98  
% 1.93/0.98  ------ Abstraction refinement Options
% 1.93/0.98  
% 1.93/0.98  --abstr_ref                             []
% 1.93/0.98  --abstr_ref_prep                        false
% 1.93/0.98  --abstr_ref_until_sat                   false
% 1.93/0.98  --abstr_ref_sig_restrict                funpre
% 1.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.98  --abstr_ref_under                       []
% 1.93/0.98  
% 1.93/0.98  ------ SAT Options
% 1.93/0.98  
% 1.93/0.98  --sat_mode                              false
% 1.93/0.98  --sat_fm_restart_options                ""
% 1.93/0.98  --sat_gr_def                            false
% 1.93/0.98  --sat_epr_types                         true
% 1.93/0.98  --sat_non_cyclic_types                  false
% 1.93/0.98  --sat_finite_models                     false
% 1.93/0.98  --sat_fm_lemmas                         false
% 1.93/0.98  --sat_fm_prep                           false
% 1.93/0.98  --sat_fm_uc_incr                        true
% 1.93/0.98  --sat_out_model                         small
% 1.93/0.98  --sat_out_clauses                       false
% 1.93/0.98  
% 1.93/0.98  ------ QBF Options
% 1.93/0.98  
% 1.93/0.98  --qbf_mode                              false
% 1.93/0.98  --qbf_elim_univ                         false
% 1.93/0.98  --qbf_dom_inst                          none
% 1.93/0.98  --qbf_dom_pre_inst                      false
% 1.93/0.98  --qbf_sk_in                             false
% 1.93/0.98  --qbf_pred_elim                         true
% 1.93/0.98  --qbf_split                             512
% 1.93/0.98  
% 1.93/0.98  ------ BMC1 Options
% 1.93/0.98  
% 1.93/0.98  --bmc1_incremental                      false
% 1.93/0.98  --bmc1_axioms                           reachable_all
% 1.93/0.98  --bmc1_min_bound                        0
% 1.93/0.98  --bmc1_max_bound                        -1
% 1.93/0.98  --bmc1_max_bound_default                -1
% 1.93/0.98  --bmc1_symbol_reachability              true
% 1.93/0.98  --bmc1_property_lemmas                  false
% 1.93/0.98  --bmc1_k_induction                      false
% 1.93/0.98  --bmc1_non_equiv_states                 false
% 1.93/0.98  --bmc1_deadlock                         false
% 1.93/0.98  --bmc1_ucm                              false
% 1.93/0.98  --bmc1_add_unsat_core                   none
% 1.93/0.98  --bmc1_unsat_core_children              false
% 1.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.98  --bmc1_out_stat                         full
% 1.93/0.98  --bmc1_ground_init                      false
% 1.93/0.98  --bmc1_pre_inst_next_state              false
% 1.93/0.98  --bmc1_pre_inst_state                   false
% 1.93/0.98  --bmc1_pre_inst_reach_state             false
% 1.93/0.98  --bmc1_out_unsat_core                   false
% 1.93/0.98  --bmc1_aig_witness_out                  false
% 1.93/0.98  --bmc1_verbose                          false
% 1.93/0.98  --bmc1_dump_clauses_tptp                false
% 1.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.98  --bmc1_dump_file                        -
% 1.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.98  --bmc1_ucm_extend_mode                  1
% 1.93/0.98  --bmc1_ucm_init_mode                    2
% 1.93/0.98  --bmc1_ucm_cone_mode                    none
% 1.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.98  --bmc1_ucm_relax_model                  4
% 1.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.98  --bmc1_ucm_layered_model                none
% 1.93/0.98  --bmc1_ucm_max_lemma_size               10
% 1.93/0.98  
% 1.93/0.98  ------ AIG Options
% 1.93/0.98  
% 1.93/0.98  --aig_mode                              false
% 1.93/0.98  
% 1.93/0.98  ------ Instantiation Options
% 1.93/0.98  
% 1.93/0.98  --instantiation_flag                    true
% 1.93/0.98  --inst_sos_flag                         false
% 1.93/0.98  --inst_sos_phase                        true
% 1.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel_side                     num_symb
% 1.93/0.98  --inst_solver_per_active                1400
% 1.93/0.98  --inst_solver_calls_frac                1.
% 1.93/0.98  --inst_passive_queue_type               priority_queues
% 1.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.98  --inst_passive_queues_freq              [25;2]
% 1.93/0.98  --inst_dismatching                      true
% 1.93/0.98  --inst_eager_unprocessed_to_passive     true
% 1.93/0.98  --inst_prop_sim_given                   true
% 1.93/0.98  --inst_prop_sim_new                     false
% 1.93/0.98  --inst_subs_new                         false
% 1.93/0.98  --inst_eq_res_simp                      false
% 1.93/0.98  --inst_subs_given                       false
% 1.93/0.98  --inst_orphan_elimination               true
% 1.93/0.98  --inst_learning_loop_flag               true
% 1.93/0.98  --inst_learning_start                   3000
% 1.93/0.98  --inst_learning_factor                  2
% 1.93/0.98  --inst_start_prop_sim_after_learn       3
% 1.93/0.98  --inst_sel_renew                        solver
% 1.93/0.98  --inst_lit_activity_flag                true
% 1.93/0.98  --inst_restr_to_given                   false
% 1.93/0.98  --inst_activity_threshold               500
% 1.93/0.98  --inst_out_proof                        true
% 1.93/0.98  
% 1.93/0.98  ------ Resolution Options
% 1.93/0.98  
% 1.93/0.98  --resolution_flag                       true
% 1.93/0.98  --res_lit_sel                           adaptive
% 1.93/0.98  --res_lit_sel_side                      none
% 1.93/0.98  --res_ordering                          kbo
% 1.93/0.98  --res_to_prop_solver                    active
% 1.93/0.98  --res_prop_simpl_new                    false
% 1.93/0.98  --res_prop_simpl_given                  true
% 1.93/0.98  --res_passive_queue_type                priority_queues
% 1.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.98  --res_passive_queues_freq               [15;5]
% 1.93/0.98  --res_forward_subs                      full
% 1.93/0.98  --res_backward_subs                     full
% 1.93/0.98  --res_forward_subs_resolution           true
% 1.93/0.98  --res_backward_subs_resolution          true
% 1.93/0.98  --res_orphan_elimination                true
% 1.93/0.98  --res_time_limit                        2.
% 1.93/0.98  --res_out_proof                         true
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Options
% 1.93/0.98  
% 1.93/0.98  --superposition_flag                    true
% 1.93/0.98  --sup_passive_queue_type                priority_queues
% 1.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.98  --demod_completeness_check              fast
% 1.93/0.98  --demod_use_ground                      true
% 1.93/0.98  --sup_to_prop_solver                    passive
% 1.93/0.98  --sup_prop_simpl_new                    true
% 1.93/0.98  --sup_prop_simpl_given                  true
% 1.93/0.98  --sup_fun_splitting                     false
% 1.93/0.98  --sup_smt_interval                      50000
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Simplification Setup
% 1.93/0.98  
% 1.93/0.98  --sup_indices_passive                   []
% 1.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_full_bw                           [BwDemod]
% 1.93/0.98  --sup_immed_triv                        [TrivRules]
% 1.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_immed_bw_main                     []
% 1.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  
% 1.93/0.98  ------ Combination Options
% 1.93/0.98  
% 1.93/0.98  --comb_res_mult                         3
% 1.93/0.98  --comb_sup_mult                         2
% 1.93/0.98  --comb_inst_mult                        10
% 1.93/0.98  
% 1.93/0.98  ------ Debug Options
% 1.93/0.98  
% 1.93/0.98  --dbg_backtrace                         false
% 1.93/0.98  --dbg_dump_prop_clauses                 false
% 1.93/0.98  --dbg_dump_prop_clauses_file            -
% 1.93/0.98  --dbg_out_stat                          false
% 1.93/0.98  ------ Parsing...
% 1.93/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.98  ------ Proving...
% 1.93/0.98  ------ Problem Properties 
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  clauses                                 22
% 1.93/0.98  conjectures                             2
% 1.93/0.98  EPR                                     7
% 1.93/0.98  Horn                                    18
% 1.93/0.98  unary                                   3
% 1.93/0.98  binary                                  16
% 1.93/0.98  lits                                    44
% 1.93/0.98  lits eq                                 21
% 1.93/0.98  fd_pure                                 0
% 1.93/0.98  fd_pseudo                               0
% 1.93/0.98  fd_cond                                 0
% 1.93/0.98  fd_pseudo_cond                          1
% 1.93/0.98  AC symbols                              0
% 1.93/0.98  
% 1.93/0.98  ------ Schedule dynamic 5 is on 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  ------ 
% 1.93/0.98  Current options:
% 1.93/0.98  ------ 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options
% 1.93/0.98  
% 1.93/0.98  --out_options                           all
% 1.93/0.98  --tptp_safe_out                         true
% 1.93/0.98  --problem_path                          ""
% 1.93/0.98  --include_path                          ""
% 1.93/0.98  --clausifier                            res/vclausify_rel
% 1.93/0.98  --clausifier_options                    --mode clausify
% 1.93/0.98  --stdin                                 false
% 1.93/0.98  --stats_out                             all
% 1.93/0.98  
% 1.93/0.98  ------ General Options
% 1.93/0.98  
% 1.93/0.98  --fof                                   false
% 1.93/0.98  --time_out_real                         305.
% 1.93/0.98  --time_out_virtual                      -1.
% 1.93/0.98  --symbol_type_check                     false
% 1.93/0.98  --clausify_out                          false
% 1.93/0.98  --sig_cnt_out                           false
% 1.93/0.98  --trig_cnt_out                          false
% 1.93/0.98  --trig_cnt_out_tolerance                1.
% 1.93/0.98  --trig_cnt_out_sk_spl                   false
% 1.93/0.98  --abstr_cl_out                          false
% 1.93/0.98  
% 1.93/0.98  ------ Global Options
% 1.93/0.98  
% 1.93/0.98  --schedule                              default
% 1.93/0.98  --add_important_lit                     false
% 1.93/0.98  --prop_solver_per_cl                    1000
% 1.93/0.98  --min_unsat_core                        false
% 1.93/0.98  --soft_assumptions                      false
% 1.93/0.98  --soft_lemma_size                       3
% 1.93/0.98  --prop_impl_unit_size                   0
% 1.93/0.98  --prop_impl_unit                        []
% 1.93/0.98  --share_sel_clauses                     true
% 1.93/0.98  --reset_solvers                         false
% 1.93/0.98  --bc_imp_inh                            [conj_cone]
% 1.93/0.98  --conj_cone_tolerance                   3.
% 1.93/0.98  --extra_neg_conj                        none
% 1.93/0.98  --large_theory_mode                     true
% 1.93/0.98  --prolific_symb_bound                   200
% 1.93/0.98  --lt_threshold                          2000
% 1.93/0.98  --clause_weak_htbl                      true
% 1.93/0.98  --gc_record_bc_elim                     false
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing Options
% 1.93/0.98  
% 1.93/0.98  --preprocessing_flag                    true
% 1.93/0.98  --time_out_prep_mult                    0.1
% 1.93/0.98  --splitting_mode                        input
% 1.93/0.98  --splitting_grd                         true
% 1.93/0.98  --splitting_cvd                         false
% 1.93/0.98  --splitting_cvd_svl                     false
% 1.93/0.98  --splitting_nvd                         32
% 1.93/0.98  --sub_typing                            true
% 1.93/0.98  --prep_gs_sim                           true
% 1.93/0.98  --prep_unflatten                        true
% 1.93/0.98  --prep_res_sim                          true
% 1.93/0.98  --prep_upred                            true
% 1.93/0.98  --prep_sem_filter                       exhaustive
% 1.93/0.98  --prep_sem_filter_out                   false
% 1.93/0.98  --pred_elim                             true
% 1.93/0.98  --res_sim_input                         true
% 1.93/0.98  --eq_ax_congr_red                       true
% 1.93/0.98  --pure_diseq_elim                       true
% 1.93/0.98  --brand_transform                       false
% 1.93/0.98  --non_eq_to_eq                          false
% 1.93/0.98  --prep_def_merge                        true
% 1.93/0.98  --prep_def_merge_prop_impl              false
% 1.93/0.98  --prep_def_merge_mbd                    true
% 1.93/0.98  --prep_def_merge_tr_red                 false
% 1.93/0.98  --prep_def_merge_tr_cl                  false
% 1.93/0.98  --smt_preprocessing                     true
% 1.93/0.98  --smt_ac_axioms                         fast
% 1.93/0.98  --preprocessed_out                      false
% 1.93/0.98  --preprocessed_stats                    false
% 1.93/0.98  
% 1.93/0.98  ------ Abstraction refinement Options
% 1.93/0.98  
% 1.93/0.98  --abstr_ref                             []
% 1.93/0.98  --abstr_ref_prep                        false
% 1.93/0.98  --abstr_ref_until_sat                   false
% 1.93/0.98  --abstr_ref_sig_restrict                funpre
% 1.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.98  --abstr_ref_under                       []
% 1.93/0.98  
% 1.93/0.98  ------ SAT Options
% 1.93/0.98  
% 1.93/0.98  --sat_mode                              false
% 1.93/0.98  --sat_fm_restart_options                ""
% 1.93/0.98  --sat_gr_def                            false
% 1.93/0.98  --sat_epr_types                         true
% 1.93/0.98  --sat_non_cyclic_types                  false
% 1.93/0.98  --sat_finite_models                     false
% 1.93/0.98  --sat_fm_lemmas                         false
% 1.93/0.98  --sat_fm_prep                           false
% 1.93/0.98  --sat_fm_uc_incr                        true
% 1.93/0.98  --sat_out_model                         small
% 1.93/0.98  --sat_out_clauses                       false
% 1.93/0.98  
% 1.93/0.98  ------ QBF Options
% 1.93/0.98  
% 1.93/0.98  --qbf_mode                              false
% 1.93/0.98  --qbf_elim_univ                         false
% 1.93/0.98  --qbf_dom_inst                          none
% 1.93/0.98  --qbf_dom_pre_inst                      false
% 1.93/0.98  --qbf_sk_in                             false
% 1.93/0.98  --qbf_pred_elim                         true
% 1.93/0.98  --qbf_split                             512
% 1.93/0.98  
% 1.93/0.98  ------ BMC1 Options
% 1.93/0.98  
% 1.93/0.98  --bmc1_incremental                      false
% 1.93/0.98  --bmc1_axioms                           reachable_all
% 1.93/0.98  --bmc1_min_bound                        0
% 1.93/0.98  --bmc1_max_bound                        -1
% 1.93/0.98  --bmc1_max_bound_default                -1
% 1.93/0.98  --bmc1_symbol_reachability              true
% 1.93/0.98  --bmc1_property_lemmas                  false
% 1.93/0.98  --bmc1_k_induction                      false
% 1.93/0.98  --bmc1_non_equiv_states                 false
% 1.93/0.98  --bmc1_deadlock                         false
% 1.93/0.98  --bmc1_ucm                              false
% 1.93/0.98  --bmc1_add_unsat_core                   none
% 1.93/0.98  --bmc1_unsat_core_children              false
% 1.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.98  --bmc1_out_stat                         full
% 1.93/0.98  --bmc1_ground_init                      false
% 1.93/0.98  --bmc1_pre_inst_next_state              false
% 1.93/0.98  --bmc1_pre_inst_state                   false
% 1.93/0.98  --bmc1_pre_inst_reach_state             false
% 1.93/0.98  --bmc1_out_unsat_core                   false
% 1.93/0.98  --bmc1_aig_witness_out                  false
% 1.93/0.98  --bmc1_verbose                          false
% 1.93/0.98  --bmc1_dump_clauses_tptp                false
% 1.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.98  --bmc1_dump_file                        -
% 1.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.98  --bmc1_ucm_extend_mode                  1
% 1.93/0.98  --bmc1_ucm_init_mode                    2
% 1.93/0.98  --bmc1_ucm_cone_mode                    none
% 1.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.98  --bmc1_ucm_relax_model                  4
% 1.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.98  --bmc1_ucm_layered_model                none
% 1.93/0.98  --bmc1_ucm_max_lemma_size               10
% 1.93/0.98  
% 1.93/0.98  ------ AIG Options
% 1.93/0.98  
% 1.93/0.98  --aig_mode                              false
% 1.93/0.98  
% 1.93/0.98  ------ Instantiation Options
% 1.93/0.98  
% 1.93/0.98  --instantiation_flag                    true
% 1.93/0.98  --inst_sos_flag                         false
% 1.93/0.98  --inst_sos_phase                        true
% 1.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel_side                     none
% 1.93/0.98  --inst_solver_per_active                1400
% 1.93/0.98  --inst_solver_calls_frac                1.
% 1.93/0.98  --inst_passive_queue_type               priority_queues
% 1.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.98  --inst_passive_queues_freq              [25;2]
% 1.93/0.98  --inst_dismatching                      true
% 1.93/0.98  --inst_eager_unprocessed_to_passive     true
% 1.93/0.98  --inst_prop_sim_given                   true
% 1.93/0.98  --inst_prop_sim_new                     false
% 1.93/0.98  --inst_subs_new                         false
% 1.93/0.98  --inst_eq_res_simp                      false
% 1.93/0.98  --inst_subs_given                       false
% 1.93/0.98  --inst_orphan_elimination               true
% 1.93/0.98  --inst_learning_loop_flag               true
% 1.93/0.98  --inst_learning_start                   3000
% 1.93/0.98  --inst_learning_factor                  2
% 1.93/0.98  --inst_start_prop_sim_after_learn       3
% 1.93/0.98  --inst_sel_renew                        solver
% 1.93/0.98  --inst_lit_activity_flag                true
% 1.93/0.98  --inst_restr_to_given                   false
% 1.93/0.98  --inst_activity_threshold               500
% 1.93/0.98  --inst_out_proof                        true
% 1.93/0.98  
% 1.93/0.98  ------ Resolution Options
% 1.93/0.98  
% 1.93/0.98  --resolution_flag                       false
% 1.93/0.98  --res_lit_sel                           adaptive
% 1.93/0.98  --res_lit_sel_side                      none
% 1.93/0.98  --res_ordering                          kbo
% 1.93/0.98  --res_to_prop_solver                    active
% 1.93/0.98  --res_prop_simpl_new                    false
% 1.93/0.98  --res_prop_simpl_given                  true
% 1.93/0.98  --res_passive_queue_type                priority_queues
% 1.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.98  --res_passive_queues_freq               [15;5]
% 1.93/0.98  --res_forward_subs                      full
% 1.93/0.98  --res_backward_subs                     full
% 1.93/0.98  --res_forward_subs_resolution           true
% 1.93/0.98  --res_backward_subs_resolution          true
% 1.93/0.98  --res_orphan_elimination                true
% 1.93/0.98  --res_time_limit                        2.
% 1.93/0.98  --res_out_proof                         true
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Options
% 1.93/0.98  
% 1.93/0.98  --superposition_flag                    true
% 1.93/0.98  --sup_passive_queue_type                priority_queues
% 1.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.98  --demod_completeness_check              fast
% 1.93/0.98  --demod_use_ground                      true
% 1.93/0.98  --sup_to_prop_solver                    passive
% 1.93/0.98  --sup_prop_simpl_new                    true
% 1.93/0.98  --sup_prop_simpl_given                  true
% 1.93/0.98  --sup_fun_splitting                     false
% 1.93/0.98  --sup_smt_interval                      50000
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Simplification Setup
% 1.93/0.98  
% 1.93/0.98  --sup_indices_passive                   []
% 1.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_full_bw                           [BwDemod]
% 1.93/0.98  --sup_immed_triv                        [TrivRules]
% 1.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_immed_bw_main                     []
% 1.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  
% 1.93/0.98  ------ Combination Options
% 1.93/0.98  
% 1.93/0.98  --comb_res_mult                         3
% 1.93/0.98  --comb_sup_mult                         2
% 1.93/0.98  --comb_inst_mult                        10
% 1.93/0.98  
% 1.93/0.98  ------ Debug Options
% 1.93/0.98  
% 1.93/0.98  --dbg_backtrace                         false
% 1.93/0.98  --dbg_dump_prop_clauses                 false
% 1.93/0.98  --dbg_dump_prop_clauses_file            -
% 1.93/0.98  --dbg_out_stat                          false
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  ------ Proving...
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  % SZS status Theorem for theBenchmark.p
% 1.93/0.98  
% 1.93/0.98   Resolution empty clause
% 1.93/0.98  
% 1.93/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/0.98  
% 1.93/0.98  fof(f7,axiom,(
% 1.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f26,plain,(
% 1.93/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f7])).
% 1.93/0.98  
% 1.93/0.98  fof(f52,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f26])).
% 1.93/0.98  
% 1.93/0.98  fof(f15,conjecture,(
% 1.93/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f16,negated_conjecture,(
% 1.93/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.93/0.98    inference(negated_conjecture,[],[f15])).
% 1.93/0.98  
% 1.93/0.98  fof(f37,plain,(
% 1.93/0.98    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 1.93/0.98    inference(ennf_transformation,[],[f16])).
% 1.93/0.98  
% 1.93/0.98  fof(f38,plain,(
% 1.93/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 1.93/0.98    inference(flattening,[],[f37])).
% 1.93/0.98  
% 1.93/0.98  fof(f42,plain,(
% 1.93/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f43,plain,(
% 1.93/0.98    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 1.93/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42])).
% 1.93/0.98  
% 1.93/0.98  fof(f66,plain,(
% 1.93/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f5,axiom,(
% 1.93/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f22,plain,(
% 1.93/0.98    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.93/0.98    inference(ennf_transformation,[],[f5])).
% 1.93/0.98  
% 1.93/0.98  fof(f23,plain,(
% 1.93/0.98    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(flattening,[],[f22])).
% 1.93/0.98  
% 1.93/0.98  fof(f50,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f23])).
% 1.93/0.98  
% 1.93/0.98  fof(f63,plain,(
% 1.93/0.98    v1_funct_1(sK2)),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f9,axiom,(
% 1.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f28,plain,(
% 1.93/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f9])).
% 1.93/0.98  
% 1.93/0.98  fof(f54,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f28])).
% 1.93/0.98  
% 1.93/0.98  fof(f14,axiom,(
% 1.93/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f35,plain,(
% 1.93/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.93/0.98    inference(ennf_transformation,[],[f14])).
% 1.93/0.98  
% 1.93/0.98  fof(f36,plain,(
% 1.93/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.93/0.98    inference(flattening,[],[f35])).
% 1.93/0.98  
% 1.93/0.98  fof(f62,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f36])).
% 1.93/0.98  
% 1.93/0.98  fof(f64,plain,(
% 1.93/0.98    v1_funct_2(sK2,sK0,sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f11,axiom,(
% 1.93/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f30,plain,(
% 1.93/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f11])).
% 1.93/0.98  
% 1.93/0.98  fof(f56,plain,(
% 1.93/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f30])).
% 1.93/0.98  
% 1.93/0.98  fof(f68,plain,(
% 1.93/0.98    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f10,axiom,(
% 1.93/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f29,plain,(
% 1.93/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f10])).
% 1.93/0.98  
% 1.93/0.98  fof(f55,plain,(
% 1.93/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f29])).
% 1.93/0.98  
% 1.93/0.98  fof(f67,plain,(
% 1.93/0.98    r1_tarski(sK1,sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f3,axiom,(
% 1.93/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f19,plain,(
% 1.93/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(ennf_transformation,[],[f3])).
% 1.93/0.98  
% 1.93/0.98  fof(f48,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f19])).
% 1.93/0.98  
% 1.93/0.98  fof(f6,axiom,(
% 1.93/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f24,plain,(
% 1.93/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.93/0.98    inference(ennf_transformation,[],[f6])).
% 1.93/0.98  
% 1.93/0.98  fof(f25,plain,(
% 1.93/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(flattening,[],[f24])).
% 1.93/0.98  
% 1.93/0.98  fof(f51,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f25])).
% 1.93/0.98  
% 1.93/0.98  fof(f12,axiom,(
% 1.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f31,plain,(
% 1.93/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f12])).
% 1.93/0.98  
% 1.93/0.98  fof(f32,plain,(
% 1.93/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(flattening,[],[f31])).
% 1.93/0.98  
% 1.93/0.98  fof(f58,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f32])).
% 1.93/0.98  
% 1.93/0.98  fof(f65,plain,(
% 1.93/0.98    v3_funct_2(sK2,sK0,sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f43])).
% 1.93/0.98  
% 1.93/0.98  fof(f1,axiom,(
% 1.93/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f39,plain,(
% 1.93/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.98    inference(nnf_transformation,[],[f1])).
% 1.93/0.98  
% 1.93/0.98  fof(f40,plain,(
% 1.93/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.98    inference(flattening,[],[f39])).
% 1.93/0.98  
% 1.93/0.98  fof(f46,plain,(
% 1.93/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f44,plain,(
% 1.93/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f70,plain,(
% 1.93/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.93/0.98    inference(equality_resolution,[],[f44])).
% 1.93/0.98  
% 1.93/0.98  fof(f2,axiom,(
% 1.93/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f18,plain,(
% 1.93/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.98    inference(ennf_transformation,[],[f2])).
% 1.93/0.98  
% 1.93/0.98  fof(f47,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f18])).
% 1.93/0.98  
% 1.93/0.98  fof(f4,axiom,(
% 1.93/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f20,plain,(
% 1.93/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(ennf_transformation,[],[f4])).
% 1.93/0.98  
% 1.93/0.98  fof(f21,plain,(
% 1.93/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(flattening,[],[f20])).
% 1.93/0.98  
% 1.93/0.98  fof(f49,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f21])).
% 1.93/0.98  
% 1.93/0.98  fof(f59,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f32])).
% 1.93/0.98  
% 1.93/0.98  fof(f13,axiom,(
% 1.93/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f33,plain,(
% 1.93/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.93/0.98    inference(ennf_transformation,[],[f13])).
% 1.93/0.98  
% 1.93/0.98  fof(f34,plain,(
% 1.93/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(flattening,[],[f33])).
% 1.93/0.98  
% 1.93/0.98  fof(f41,plain,(
% 1.93/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.93/0.98    inference(nnf_transformation,[],[f34])).
% 1.93/0.98  
% 1.93/0.98  fof(f60,plain,(
% 1.93/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f41])).
% 1.93/0.98  
% 1.93/0.98  fof(f8,axiom,(
% 1.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f17,plain,(
% 1.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.93/0.98    inference(pure_predicate_removal,[],[f8])).
% 1.93/0.98  
% 1.93/0.98  fof(f27,plain,(
% 1.93/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.98    inference(ennf_transformation,[],[f17])).
% 1.93/0.98  
% 1.93/0.98  fof(f53,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.98    inference(cnf_transformation,[],[f27])).
% 1.93/0.98  
% 1.93/0.98  cnf(c_8,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_21,negated_conjecture,
% 1.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.93/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_369,plain,
% 1.93/0.98      ( v1_relat_1(X0)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sK2 != X0 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_370,plain,
% 1.93/0.98      ( v1_relat_1(sK2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_369]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_6,plain,
% 1.93/0.98      ( ~ v1_funct_1(X0)
% 1.93/0.98      | ~ v1_relat_1(X0)
% 1.93/0.98      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 1.93/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_24,negated_conjecture,
% 1.93/0.98      ( v1_funct_1(sK2) ),
% 1.93/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_327,plain,
% 1.93/0.98      ( ~ v1_relat_1(X0)
% 1.93/0.98      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 1.93/0.98      | sK2 != X0 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_328,plain,
% 1.93/0.98      ( ~ v1_relat_1(sK2)
% 1.93/0.98      | k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_327]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_462,plain,
% 1.93/0.98      ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(resolution,[status(thm)],[c_370,c_328]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_579,plain,
% 1.93/0.98      ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 1.93/0.98      | ~ sP4_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 1.93/0.98                [c_462]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_850,plain,
% 1.93/0.98      ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 1.93/0.98      | sP4_iProver_split != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_372,plain,
% 1.93/0.98      ( v1_relat_1(sK2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_370]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_582,plain,( X0 = X0 ),theory(equality) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_963,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_582]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1410,plain,
% 1.93/0.98      ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_850,c_328,c_372,c_963]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_10,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_360,plain,
% 1.93/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sK2 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_361,plain,
% 1.93/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_360]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_974,plain,
% 1.93/0.98      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_361]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_18,plain,
% 1.93/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.93/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_23,negated_conjecture,
% 1.93/0.98      ( v1_funct_2(sK2,sK0,sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_267,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | k1_relset_1(X1,X1,X0) = X1
% 1.93/0.98      | sK2 != X0
% 1.93/0.98      | sK0 != X1 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_268,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.93/0.98      | ~ v1_funct_1(sK2)
% 1.93/0.98      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_267]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_270,plain,
% 1.93/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_268,c_24,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_975,plain,
% 1.93/0.98      ( k1_relat_1(sK2) = sK0 ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_974,c_270]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1413,plain,
% 1.93/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,sK0)) ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_1410,c_975]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_12,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_342,plain,
% 1.93/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sK2 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_343,plain,
% 1.93/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_342]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_991,plain,
% 1.93/0.98      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_343]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_19,negated_conjecture,
% 1.93/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 1.93/0.98      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.93/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1012,plain,
% 1.93/0.98      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 1.93/0.98      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_991,c_19]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1013,plain,
% 1.93/0.98      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 1.93/0.98      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_1012,c_991]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_11,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_351,plain,
% 1.93/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sK2 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_352,plain,
% 1.93/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_351]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_995,plain,
% 1.93/0.98      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_352]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1224,plain,
% 1.93/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 1.93/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_1013,c_995]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1416,plain,
% 1.93/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 1.93/0.98      | k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != sK1 ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_1413,c_1224]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_20,negated_conjecture,
% 1.93/0.98      ( r1_tarski(sK1,sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_4,plain,
% 1.93/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_499,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 1.93/0.98      | sK2 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_370]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_500,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_499]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_573,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | ~ sP1_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.93/0.98                [c_500]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_612,plain,
% 1.93/0.98      ( ~ sP1_iProver_split
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_573]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_7,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 1.93/0.98      | ~ v2_funct_1(X1)
% 1.93/0.98      | ~ v1_funct_1(X1)
% 1.93/0.98      | ~ v1_relat_1(X1)
% 1.93/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 1.93/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_14,plain,
% 1.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.98      | v2_funct_1(X0)
% 1.93/0.98      | ~ v1_funct_1(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_22,negated_conjecture,
% 1.93/0.98      ( v3_funct_2(sK2,sK0,sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_276,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.98      | v2_funct_1(X0)
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | sK2 != X0
% 1.93/0.98      | sK0 != X1
% 1.93/0.98      | sK0 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_277,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.93/0.98      | v2_funct_1(sK2)
% 1.93/0.98      | ~ v1_funct_1(sK2) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_276]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_279,plain,
% 1.93/0.98      ( v2_funct_1(sK2) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_277,c_24,c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_302,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 1.93/0.98      | ~ v1_funct_1(X1)
% 1.93/0.98      | ~ v1_relat_1(X1)
% 1.93/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 1.93/0.98      | sK2 != X1 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_279]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_303,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.93/0.98      | ~ v1_funct_1(sK2)
% 1.93/0.98      | ~ v1_relat_1(sK2)
% 1.93/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_302]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_307,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.93/0.98      | ~ v1_relat_1(sK2)
% 1.93/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 1.93/0.98      inference(global_propositional_subsumption,[status(thm)],[c_303,c_24]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_470,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.93/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(resolution,[status(thm)],[c_370,c_307]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_578,plain,
% 1.93/0.98      ( sP3_iProver_split | sP1_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[])],
% 1.93/0.98                [c_470]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_0,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.93/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1002,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1037,plain,
% 1.93/0.98      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1002]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f70]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1038,plain,
% 1.93/0.98      ( r1_tarski(sK1,sK1) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_577,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.93/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 1.93/0.98      | ~ sP3_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 1.93/0.98                [c_470]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1149,plain,
% 1.93/0.98      ( ~ r1_tarski(sK1,k1_relat_1(sK2))
% 1.93/0.98      | ~ sP3_iProver_split
% 1.93/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_577]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_584,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.93/0.98      theory(equality) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1032,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,X1)
% 1.93/0.98      | r1_tarski(X2,k1_relat_1(sK2))
% 1.93/0.98      | X2 != X0
% 1.93/0.98      | k1_relat_1(sK2) != X1 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_584]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1164,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,X1)
% 1.93/0.98      | r1_tarski(sK1,k1_relat_1(sK2))
% 1.93/0.98      | k1_relat_1(sK2) != X1
% 1.93/0.98      | sK1 != X0 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1319,plain,
% 1.93/0.98      ( ~ r1_tarski(sK1,X0)
% 1.93/0.98      | r1_tarski(sK1,k1_relat_1(sK2))
% 1.93/0.98      | k1_relat_1(sK2) != X0
% 1.93/0.98      | sK1 != sK1 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1321,plain,
% 1.93/0.98      ( r1_tarski(sK1,k1_relat_1(sK2))
% 1.93/0.98      | ~ r1_tarski(sK1,sK0)
% 1.93/0.98      | k1_relat_1(sK2) != sK0
% 1.93/0.98      | sK1 != sK1 ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1319]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2181,plain,
% 1.93/0.98      ( k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != sK1 ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_1416,c_20,c_612,c_578,c_963,c_975,c_1037,c_1038,c_1149,
% 1.93/0.98                 c_1321]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_852,plain,
% 1.93/0.98      ( r1_tarski(sK1,sK0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3,plain,
% 1.93/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.93/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_853,plain,
% 1.93/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1060,plain,
% 1.93/0.98      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 1.93/0.98      inference(superposition,[status(thm)],[c_852,c_853]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_854,plain,
% 1.93/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_5,plain,
% 1.93/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.93/0.98      | ~ v1_relat_1(X0)
% 1.93/0.98      | k7_relat_1(X0,X1) = X0 ),
% 1.93/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_484,plain,
% 1.93/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.93/0.98      | k7_relat_1(X0,X1) = X0
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sK2 != X0 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_370]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_485,plain,
% 1.93/0.98      ( ~ r1_tarski(k1_relat_1(sK2),X0)
% 1.93/0.98      | k7_relat_1(sK2,X0) = sK2
% 1.93/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_484]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_575,plain,
% 1.93/0.98      ( ~ r1_tarski(k1_relat_1(sK2),X0)
% 1.93/0.98      | k7_relat_1(sK2,X0) = sK2
% 1.93/0.98      | ~ sP2_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.93/0.98                [c_485]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_844,plain,
% 1.93/0.98      ( k7_relat_1(sK2,X0) = sK2
% 1.93/0.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 1.93/0.98      | sP2_iProver_split != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_611,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sP1_iProver_split != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_613,plain,
% 1.93/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.98      | sP1_iProver_split != iProver_top ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_611]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_576,plain,
% 1.93/0.98      ( sP2_iProver_split | sP1_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[])],
% 1.93/0.98                [c_485]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_617,plain,
% 1.93/0.98      ( sP2_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_618,plain,
% 1.93/0.98      ( k7_relat_1(sK2,X0) = sK2
% 1.93/0.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 1.93/0.98      | sP2_iProver_split != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1418,plain,
% 1.93/0.98      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 1.93/0.98      | k7_relat_1(sK2,X0) = sK2 ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_844,c_613,c_617,c_618,c_963]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1419,plain,
% 1.93/0.99      ( k7_relat_1(sK2,X0) = sK2
% 1.93/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_1418]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1424,plain,
% 1.93/0.99      ( k7_relat_1(sK2,X0) = sK2 | r1_tarski(sK0,X0) != iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_1419,c_975]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1430,plain,
% 1.93/0.99      ( k7_relat_1(sK2,sK0) = sK2 ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_854,c_1424]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_572,plain,
% 1.93/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
% 1.93/0.99      | ~ sP0_iProver_split ),
% 1.93/0.99      inference(splitting,
% 1.93/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.93/0.99                [c_500]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_842,plain,
% 1.93/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
% 1.93/0.99      | sP0_iProver_split != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_574,plain,
% 1.93/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 1.93/0.99      inference(splitting,
% 1.93/0.99                [splitting(split),new_symbols(definition,[])],
% 1.93/0.99                [c_500]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1355,plain,
% 1.93/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_842,c_574,c_612,c_572,c_963]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1522,plain,
% 1.93/0.99      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_1430,c_1355]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_13,plain,
% 1.93/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 1.93/0.99      | v2_funct_2(X0,X2)
% 1.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.93/0.99      | ~ v1_funct_1(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_287,plain,
% 1.93/0.99      ( v2_funct_2(X0,X1)
% 1.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.93/0.99      | ~ v1_funct_1(X0)
% 1.93/0.99      | sK2 != X0
% 1.93/0.99      | sK0 != X2
% 1.93/0.99      | sK0 != X1 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_288,plain,
% 1.93/0.99      ( v2_funct_2(sK2,sK0)
% 1.93/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.93/0.99      | ~ v1_funct_1(sK2) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_290,plain,
% 1.93/0.99      ( v2_funct_2(sK2,sK0) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_288,c_24,c_21]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_17,plain,
% 1.93/0.99      ( ~ v2_funct_2(X0,X1)
% 1.93/0.99      | ~ v5_relat_1(X0,X1)
% 1.93/0.99      | ~ v1_relat_1(X0)
% 1.93/0.99      | k2_relat_1(X0) = X1 ),
% 1.93/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_9,plain,
% 1.93/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.93/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_381,plain,
% 1.93/0.99      ( v5_relat_1(X0,X1)
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | sK2 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_382,plain,
% 1.93/0.99      ( v5_relat_1(sK2,X0)
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_405,plain,
% 1.93/0.99      ( ~ v2_funct_2(X0,X1)
% 1.93/0.99      | ~ v1_relat_1(X0)
% 1.93/0.99      | X2 != X1
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(X0) = X1
% 1.93/0.99      | sK2 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_382]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_406,plain,
% 1.93/0.99      ( ~ v2_funct_2(sK2,X0)
% 1.93/0.99      | ~ v1_relat_1(sK2)
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(sK2) = X0 ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_405]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_418,plain,
% 1.93/0.99      ( ~ v2_funct_2(sK2,X0)
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(sK2) = X0 ),
% 1.93/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_406,c_370]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_449,plain,
% 1.93/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(sK2) = X1
% 1.93/0.99      | sK2 != sK2
% 1.93/0.99      | sK0 != X1 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_290,c_418]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_450,plain,
% 1.93/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(sK2) = sK0 ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_423,plain,
% 1.93/0.99      ( ~ v2_funct_2(sK2,sK0)
% 1.93/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.93/0.99      | k2_relat_1(sK2) = sK0 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_418]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1014,plain,
% 1.93/0.99      ( k2_relat_1(sK2) = sK0 ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_450,c_24,c_21,c_288,c_423,c_963]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1523,plain,
% 1.93/0.99      ( k9_relat_1(sK2,sK0) = sK0 ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_1522,c_1014]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2183,plain,
% 1.93/0.99      ( sK1 != sK1 ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_2181,c_1060,c_1523]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2184,plain,
% 1.93/0.99      ( $false ),
% 1.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_2183]) ).
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  ------                               Statistics
% 1.93/0.99  
% 1.93/0.99  ------ General
% 1.93/0.99  
% 1.93/0.99  abstr_ref_over_cycles:                  0
% 1.93/0.99  abstr_ref_under_cycles:                 0
% 1.93/0.99  gc_basic_clause_elim:                   0
% 1.93/0.99  forced_gc_time:                         0
% 1.93/0.99  parsing_time:                           0.009
% 1.93/0.99  unif_index_cands_time:                  0.
% 1.93/0.99  unif_index_add_time:                    0.
% 1.93/0.99  orderings_time:                         0.
% 1.93/0.99  out_proof_time:                         0.017
% 1.93/0.99  total_time:                             0.111
% 1.93/0.99  num_of_symbols:                         59
% 1.93/0.99  num_of_terms:                           1786
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing
% 1.93/0.99  
% 1.93/0.99  num_of_splits:                          8
% 1.93/0.99  num_of_split_atoms:                     5
% 1.93/0.99  num_of_reused_defs:                     3
% 1.93/0.99  num_eq_ax_congr_red:                    17
% 1.93/0.99  num_of_sem_filtered_clauses:            1
% 1.93/0.99  num_of_subtypes:                        0
% 1.93/0.99  monotx_restored_types:                  0
% 1.93/0.99  sat_num_of_epr_types:                   0
% 1.93/0.99  sat_num_of_non_cyclic_types:            0
% 1.93/0.99  sat_guarded_non_collapsed_types:        0
% 1.93/0.99  num_pure_diseq_elim:                    0
% 1.93/0.99  simp_replaced_by:                       0
% 1.93/0.99  res_preprocessed:                       104
% 1.93/0.99  prep_upred:                             0
% 1.93/0.99  prep_unflattend:                        23
% 1.93/0.99  smt_new_axioms:                         0
% 1.93/0.99  pred_elim_cands:                        1
% 1.93/0.99  pred_elim:                              8
% 1.93/0.99  pred_elim_cl:                           9
% 1.93/0.99  pred_elim_cycles:                       10
% 1.93/0.99  merged_defs:                            0
% 1.93/0.99  merged_defs_ncl:                        0
% 1.93/0.99  bin_hyper_res:                          0
% 1.93/0.99  prep_cycles:                            4
% 1.93/0.99  pred_elim_time:                         0.005
% 1.93/0.99  splitting_time:                         0.
% 1.93/0.99  sem_filter_time:                        0.
% 1.93/0.99  monotx_time:                            0.001
% 1.93/0.99  subtype_inf_time:                       0.
% 1.93/0.99  
% 1.93/0.99  ------ Problem properties
% 1.93/0.99  
% 1.93/0.99  clauses:                                22
% 1.93/0.99  conjectures:                            2
% 1.93/0.99  epr:                                    7
% 1.93/0.99  horn:                                   18
% 1.93/0.99  ground:                                 7
% 1.93/0.99  unary:                                  3
% 1.93/0.99  binary:                                 16
% 1.93/0.99  lits:                                   44
% 1.93/0.99  lits_eq:                                21
% 1.93/0.99  fd_pure:                                0
% 1.93/0.99  fd_pseudo:                              0
% 1.93/0.99  fd_cond:                                0
% 1.93/0.99  fd_pseudo_cond:                         1
% 1.93/0.99  ac_symbols:                             0
% 1.93/0.99  
% 1.93/0.99  ------ Propositional Solver
% 1.93/0.99  
% 1.93/0.99  prop_solver_calls:                      29
% 1.93/0.99  prop_fast_solver_calls:                 618
% 1.93/0.99  smt_solver_calls:                       0
% 1.93/0.99  smt_fast_solver_calls:                  0
% 1.93/0.99  prop_num_of_clauses:                    805
% 1.93/0.99  prop_preprocess_simplified:             3151
% 1.93/0.99  prop_fo_subsumed:                       18
% 1.93/0.99  prop_solver_time:                       0.
% 1.93/0.99  smt_solver_time:                        0.
% 1.93/0.99  smt_fast_solver_time:                   0.
% 1.93/0.99  prop_fast_solver_time:                  0.
% 1.93/0.99  prop_unsat_core_time:                   0.
% 1.93/0.99  
% 1.93/0.99  ------ QBF
% 1.93/0.99  
% 1.93/0.99  qbf_q_res:                              0
% 1.93/0.99  qbf_num_tautologies:                    0
% 1.93/0.99  qbf_prep_cycles:                        0
% 1.93/0.99  
% 1.93/0.99  ------ BMC1
% 1.93/0.99  
% 1.93/0.99  bmc1_current_bound:                     -1
% 1.93/0.99  bmc1_last_solved_bound:                 -1
% 1.93/0.99  bmc1_unsat_core_size:                   -1
% 1.93/0.99  bmc1_unsat_core_parents_size:           -1
% 1.93/0.99  bmc1_merge_next_fun:                    0
% 1.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation
% 1.93/0.99  
% 1.93/0.99  inst_num_of_clauses:                    245
% 1.93/0.99  inst_num_in_passive:                    1
% 1.93/0.99  inst_num_in_active:                     144
% 1.93/0.99  inst_num_in_unprocessed:                100
% 1.93/0.99  inst_num_of_loops:                      170
% 1.93/0.99  inst_num_of_learning_restarts:          0
% 1.93/0.99  inst_num_moves_active_passive:          20
% 1.93/0.99  inst_lit_activity:                      0
% 1.93/0.99  inst_lit_activity_moves:                0
% 1.93/0.99  inst_num_tautologies:                   0
% 1.93/0.99  inst_num_prop_implied:                  0
% 1.93/0.99  inst_num_existing_simplified:           0
% 1.93/0.99  inst_num_eq_res_simplified:             0
% 1.93/0.99  inst_num_child_elim:                    0
% 1.93/0.99  inst_num_of_dismatching_blockings:      43
% 1.93/0.99  inst_num_of_non_proper_insts:           237
% 1.93/0.99  inst_num_of_duplicates:                 0
% 1.93/0.99  inst_inst_num_from_inst_to_res:         0
% 1.93/0.99  inst_dismatching_checking_time:         0.
% 1.93/0.99  
% 1.93/0.99  ------ Resolution
% 1.93/0.99  
% 1.93/0.99  res_num_of_clauses:                     0
% 1.93/0.99  res_num_in_passive:                     0
% 1.93/0.99  res_num_in_active:                      0
% 1.93/0.99  res_num_of_loops:                       108
% 1.93/0.99  res_forward_subset_subsumed:            25
% 1.93/0.99  res_backward_subset_subsumed:           0
% 1.93/0.99  res_forward_subsumed:                   0
% 1.93/0.99  res_backward_subsumed:                  0
% 1.93/0.99  res_forward_subsumption_resolution:     2
% 1.93/0.99  res_backward_subsumption_resolution:    0
% 1.93/0.99  res_clause_to_clause_subsumption:       52
% 1.93/0.99  res_orphan_elimination:                 0
% 1.93/0.99  res_tautology_del:                      16
% 1.93/0.99  res_num_eq_res_simplified:              0
% 1.93/0.99  res_num_sel_changes:                    0
% 1.93/0.99  res_moves_from_active_to_pass:          0
% 1.93/0.99  
% 1.93/0.99  ------ Superposition
% 1.93/0.99  
% 1.93/0.99  sup_time_total:                         0.
% 1.93/0.99  sup_time_generating:                    0.
% 1.93/0.99  sup_time_sim_full:                      0.
% 1.93/0.99  sup_time_sim_immed:                     0.
% 1.93/0.99  
% 1.93/0.99  sup_num_of_clauses:                     29
% 1.93/0.99  sup_num_in_active:                      29
% 1.93/0.99  sup_num_in_passive:                     0
% 1.93/0.99  sup_num_of_loops:                       33
% 1.93/0.99  sup_fw_superposition:                   9
% 1.93/0.99  sup_bw_superposition:                   1
% 1.93/0.99  sup_immediate_simplified:               5
% 1.93/0.99  sup_given_eliminated:                   0
% 1.93/0.99  comparisons_done:                       0
% 1.93/0.99  comparisons_avoided:                    0
% 1.93/0.99  
% 1.93/0.99  ------ Simplifications
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  sim_fw_subset_subsumed:                 0
% 1.93/0.99  sim_bw_subset_subsumed:                 0
% 1.93/0.99  sim_fw_subsumed:                        1
% 1.93/0.99  sim_bw_subsumed:                        0
% 1.93/0.99  sim_fw_subsumption_res:                 0
% 1.93/0.99  sim_bw_subsumption_res:                 0
% 1.93/0.99  sim_tautology_del:                      0
% 1.93/0.99  sim_eq_tautology_del:                   1
% 1.93/0.99  sim_eq_res_simp:                        0
% 1.93/0.99  sim_fw_demodulated:                     2
% 1.93/0.99  sim_bw_demodulated:                     4
% 1.93/0.99  sim_light_normalised:                   8
% 1.93/0.99  sim_joinable_taut:                      0
% 1.93/0.99  sim_joinable_simp:                      0
% 1.93/0.99  sim_ac_normalised:                      0
% 1.93/0.99  sim_smt_subsumption:                    0
% 1.93/0.99  
%------------------------------------------------------------------------------
