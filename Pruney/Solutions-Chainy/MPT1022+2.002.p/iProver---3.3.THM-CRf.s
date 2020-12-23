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
% DateTime   : Thu Dec  3 12:07:36 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 741 expanded)
%              Number of clauses        :  107 ( 240 expanded)
%              Number of leaves         :   19 ( 145 expanded)
%              Depth                    :   22
%              Number of atoms          :  500 (3596 expanded)
%              Number of equality atoms :  213 (1080 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,
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

fof(f51,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f50])).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2662,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2661,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2667,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3707,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2661,c_2667])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_529,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_541,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_529,c_12])).

cnf(c_21,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_468,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_469,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_471,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_36,c_33])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_541,c_471])).

cnf(c_575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_579,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_33,c_577])).

cnf(c_3713,plain,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3707,c_579])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_600,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_601,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK2,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_672,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK2,X1) = X0
    | sK2 != sK2
    | sK0 != X1
    | sK0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_601])).

cnf(c_673,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k8_relset_1(sK0,sK0,sK2,sK0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_603,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k8_relset_1(sK0,sK0,sK2,sK0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_675,plain,
    ( k8_relset_1(sK0,sK0,sK2,sK0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_35,c_33,c_603])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2663,plain,
    ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3486,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK0)) = k2_relset_1(sK0,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_2661,c_2663])).

cnf(c_3792,plain,
    ( k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_675,c_3486])).

cnf(c_3877,plain,
    ( k7_relset_1(sK0,sK0,sK2,sK0) = sK0
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3713,c_3792])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2666,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4385,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2661,c_2666])).

cnf(c_4571,plain,
    ( k9_relat_1(sK2,sK0) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3877,c_4385])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2664,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4141,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relset_1(sK0,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_2661,c_2664])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2668,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4241,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2661,c_2668])).

cnf(c_4631,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4141,c_4241])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2665,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4366,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2661,c_2665])).

cnf(c_4632,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4631,c_4366,c_4385])).

cnf(c_5143,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4571,c_4632])).

cnf(c_4514,plain,
    ( k10_relat_1(sK2,sK0) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_675,c_4366])).

cnf(c_5847,plain,
    ( k1_relat_1(sK2) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5143,c_4514])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3117,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3120,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3117])).

cnf(c_2106,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3219,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_7])).

cnf(c_512,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_12])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_512])).

cnf(c_2659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_2979,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2661,c_2659])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2676,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4262,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_2676])).

cnf(c_2108,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3122,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(sK2))
    | X2 != X0
    | k1_relat_1(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_3634,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | r1_tarski(X1,k1_relat_1(sK2))
    | X1 != X0
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3122])).

cnf(c_4718,plain,
    ( r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | X0 != k1_xboole_0
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3634])).

cnf(c_4719,plain,
    ( X0 != k1_xboole_0
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4718])).

cnf(c_4721,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 != k1_xboole_0
    | r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4719])).

cnf(c_5857,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5847,c_3120,c_3219,c_4262,c_4721])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_36,c_33])).

cnf(c_483,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_460])).

cnf(c_484,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_36])).

cnf(c_2660,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_490,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2850,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2851,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2850])).

cnf(c_3395,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_40,c_490,c_2851])).

cnf(c_3396,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3395])).

cnf(c_5872,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5857,c_3396])).

cnf(c_6476,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2662,c_5872])).

cnf(c_31,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4505,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_4366,c_31])).

cnf(c_4511,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_4505,c_4366])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_585,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_36])).

cnf(c_586,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_2658,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_2744,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2658,c_579])).

cnf(c_2947,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2744,c_40,c_2851])).

cnf(c_2948,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2947])).

cnf(c_2955,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2662,c_2948])).

cnf(c_4634,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_4511,c_2955,c_4385])).

cnf(c_4635,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_4634])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6476,c_4635])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.03/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.98  
% 3.03/0.98  ------  iProver source info
% 3.03/0.98  
% 3.03/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.98  git: non_committed_changes: false
% 3.03/0.98  git: last_make_outside_of_git: false
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.98  --sat_gr_def                            false
% 3.03/0.98  --sat_epr_types                         true
% 3.03/0.98  --sat_non_cyclic_types                  false
% 3.03/0.98  --sat_finite_models                     false
% 3.03/0.98  --sat_fm_lemmas                         false
% 3.03/0.98  --sat_fm_prep                           false
% 3.03/0.98  --sat_fm_uc_incr                        true
% 3.03/0.98  --sat_out_model                         small
% 3.03/0.98  --sat_out_clauses                       false
% 3.03/0.98  
% 3.03/0.98  ------ QBF Options
% 3.03/0.98  
% 3.03/0.98  --qbf_mode                              false
% 3.03/0.98  --qbf_elim_univ                         false
% 3.03/0.98  --qbf_dom_inst                          none
% 3.03/0.98  --qbf_dom_pre_inst                      false
% 3.03/0.98  --qbf_sk_in                             false
% 3.03/0.98  --qbf_pred_elim                         true
% 3.03/0.98  --qbf_split                             512
% 3.03/0.98  
% 3.03/0.98  ------ BMC1 Options
% 3.03/0.98  
% 3.03/0.98  --bmc1_incremental                      false
% 3.03/0.98  --bmc1_axioms                           reachable_all
% 3.03/0.98  --bmc1_min_bound                        0
% 3.03/0.98  --bmc1_max_bound                        -1
% 3.03/0.98  --bmc1_max_bound_default                -1
% 3.03/0.98  --bmc1_symbol_reachability              true
% 3.03/0.98  --bmc1_property_lemmas                  false
% 3.03/0.98  --bmc1_k_induction                      false
% 3.03/0.98  --bmc1_non_equiv_states                 false
% 3.03/0.98  --bmc1_deadlock                         false
% 3.03/0.98  --bmc1_ucm                              false
% 3.03/0.98  --bmc1_add_unsat_core                   none
% 3.03/0.98  --bmc1_unsat_core_children              false
% 3.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.98  --bmc1_out_stat                         full
% 3.03/0.98  --bmc1_ground_init                      false
% 3.03/0.98  --bmc1_pre_inst_next_state              false
% 3.03/0.98  --bmc1_pre_inst_state                   false
% 3.03/0.98  --bmc1_pre_inst_reach_state             false
% 3.03/0.98  --bmc1_out_unsat_core                   false
% 3.03/0.98  --bmc1_aig_witness_out                  false
% 3.03/0.98  --bmc1_verbose                          false
% 3.03/0.98  --bmc1_dump_clauses_tptp                false
% 3.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.98  --bmc1_dump_file                        -
% 3.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.98  --bmc1_ucm_extend_mode                  1
% 3.03/0.98  --bmc1_ucm_init_mode                    2
% 3.03/0.98  --bmc1_ucm_cone_mode                    none
% 3.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.98  --bmc1_ucm_relax_model                  4
% 3.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.98  --bmc1_ucm_layered_model                none
% 3.03/0.98  --bmc1_ucm_max_lemma_size               10
% 3.03/0.98  
% 3.03/0.98  ------ AIG Options
% 3.03/0.98  
% 3.03/0.98  --aig_mode                              false
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation Options
% 3.03/0.98  
% 3.03/0.98  --instantiation_flag                    true
% 3.03/0.98  --inst_sos_flag                         false
% 3.03/0.98  --inst_sos_phase                        true
% 3.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel_side                     num_symb
% 3.03/0.98  --inst_solver_per_active                1400
% 3.03/0.98  --inst_solver_calls_frac                1.
% 3.03/0.98  --inst_passive_queue_type               priority_queues
% 3.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.98  --inst_passive_queues_freq              [25;2]
% 3.03/0.98  --inst_dismatching                      true
% 3.03/0.98  --inst_eager_unprocessed_to_passive     true
% 3.03/0.98  --inst_prop_sim_given                   true
% 3.03/0.98  --inst_prop_sim_new                     false
% 3.03/0.98  --inst_subs_new                         false
% 3.03/0.98  --inst_eq_res_simp                      false
% 3.03/0.98  --inst_subs_given                       false
% 3.03/0.98  --inst_orphan_elimination               true
% 3.03/0.98  --inst_learning_loop_flag               true
% 3.03/0.98  --inst_learning_start                   3000
% 3.03/0.98  --inst_learning_factor                  2
% 3.03/0.98  --inst_start_prop_sim_after_learn       3
% 3.03/0.98  --inst_sel_renew                        solver
% 3.03/0.98  --inst_lit_activity_flag                true
% 3.03/0.98  --inst_restr_to_given                   false
% 3.03/0.98  --inst_activity_threshold               500
% 3.03/0.98  --inst_out_proof                        true
% 3.03/0.98  
% 3.03/0.98  ------ Resolution Options
% 3.03/0.98  
% 3.03/0.98  --resolution_flag                       true
% 3.03/0.98  --res_lit_sel                           adaptive
% 3.03/0.98  --res_lit_sel_side                      none
% 3.03/0.98  --res_ordering                          kbo
% 3.03/0.98  --res_to_prop_solver                    active
% 3.03/0.98  --res_prop_simpl_new                    false
% 3.03/0.98  --res_prop_simpl_given                  true
% 3.03/0.98  --res_passive_queue_type                priority_queues
% 3.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.98  --res_passive_queues_freq               [15;5]
% 3.03/0.98  --res_forward_subs                      full
% 3.03/0.98  --res_backward_subs                     full
% 3.03/0.98  --res_forward_subs_resolution           true
% 3.03/0.98  --res_backward_subs_resolution          true
% 3.03/0.98  --res_orphan_elimination                true
% 3.03/0.98  --res_time_limit                        2.
% 3.03/0.98  --res_out_proof                         true
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Options
% 3.03/0.98  
% 3.03/0.98  --superposition_flag                    true
% 3.03/0.98  --sup_passive_queue_type                priority_queues
% 3.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.98  --demod_completeness_check              fast
% 3.03/0.98  --demod_use_ground                      true
% 3.03/0.98  --sup_to_prop_solver                    passive
% 3.03/0.98  --sup_prop_simpl_new                    true
% 3.03/0.98  --sup_prop_simpl_given                  true
% 3.03/0.98  --sup_fun_splitting                     false
% 3.03/0.98  --sup_smt_interval                      50000
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Simplification Setup
% 3.03/0.98  
% 3.03/0.98  --sup_indices_passive                   []
% 3.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_full_bw                           [BwDemod]
% 3.03/0.98  --sup_immed_triv                        [TrivRules]
% 3.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_immed_bw_main                     []
% 3.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  
% 3.03/0.98  ------ Combination Options
% 3.03/0.98  
% 3.03/0.98  --comb_res_mult                         3
% 3.03/0.98  --comb_sup_mult                         2
% 3.03/0.98  --comb_inst_mult                        10
% 3.03/0.98  
% 3.03/0.98  ------ Debug Options
% 3.03/0.98  
% 3.03/0.98  --dbg_backtrace                         false
% 3.03/0.98  --dbg_dump_prop_clauses                 false
% 3.03/0.98  --dbg_dump_prop_clauses_file            -
% 3.03/0.98  --dbg_out_stat                          false
% 3.03/0.98  ------ Parsing...
% 3.03/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.98  ------ Proving...
% 3.03/0.98  ------ Problem Properties 
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  clauses                                 26
% 3.03/0.98  conjectures                             3
% 3.03/0.98  EPR                                     4
% 3.03/0.98  Horn                                    24
% 3.03/0.98  unary                                   6
% 3.03/0.98  binary                                  12
% 3.03/0.98  lits                                    54
% 3.03/0.98  lits eq                                 24
% 3.03/0.98  fd_pure                                 0
% 3.03/0.98  fd_pseudo                               0
% 3.03/0.98  fd_cond                                 2
% 3.03/0.98  fd_pseudo_cond                          1
% 3.03/0.98  AC symbols                              0
% 3.03/0.98  
% 3.03/0.98  ------ Schedule dynamic 5 is on 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  Current options:
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.98  --sat_gr_def                            false
% 3.03/0.98  --sat_epr_types                         true
% 3.03/0.98  --sat_non_cyclic_types                  false
% 3.03/0.98  --sat_finite_models                     false
% 3.03/0.98  --sat_fm_lemmas                         false
% 3.03/0.98  --sat_fm_prep                           false
% 3.03/0.98  --sat_fm_uc_incr                        true
% 3.03/0.98  --sat_out_model                         small
% 3.03/0.98  --sat_out_clauses                       false
% 3.03/0.98  
% 3.03/0.98  ------ QBF Options
% 3.03/0.98  
% 3.03/0.98  --qbf_mode                              false
% 3.03/0.98  --qbf_elim_univ                         false
% 3.03/0.98  --qbf_dom_inst                          none
% 3.03/0.98  --qbf_dom_pre_inst                      false
% 3.03/0.98  --qbf_sk_in                             false
% 3.03/0.98  --qbf_pred_elim                         true
% 3.03/0.98  --qbf_split                             512
% 3.03/0.98  
% 3.03/0.98  ------ BMC1 Options
% 3.03/0.98  
% 3.03/0.98  --bmc1_incremental                      false
% 3.03/0.98  --bmc1_axioms                           reachable_all
% 3.03/0.98  --bmc1_min_bound                        0
% 3.03/0.98  --bmc1_max_bound                        -1
% 3.03/0.98  --bmc1_max_bound_default                -1
% 3.03/0.98  --bmc1_symbol_reachability              true
% 3.03/0.98  --bmc1_property_lemmas                  false
% 3.03/0.98  --bmc1_k_induction                      false
% 3.03/0.98  --bmc1_non_equiv_states                 false
% 3.03/0.98  --bmc1_deadlock                         false
% 3.03/0.98  --bmc1_ucm                              false
% 3.03/0.98  --bmc1_add_unsat_core                   none
% 3.03/0.98  --bmc1_unsat_core_children              false
% 3.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.98  --bmc1_out_stat                         full
% 3.03/0.98  --bmc1_ground_init                      false
% 3.03/0.98  --bmc1_pre_inst_next_state              false
% 3.03/0.98  --bmc1_pre_inst_state                   false
% 3.03/0.98  --bmc1_pre_inst_reach_state             false
% 3.03/0.98  --bmc1_out_unsat_core                   false
% 3.03/0.98  --bmc1_aig_witness_out                  false
% 3.03/0.98  --bmc1_verbose                          false
% 3.03/0.98  --bmc1_dump_clauses_tptp                false
% 3.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.98  --bmc1_dump_file                        -
% 3.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.98  --bmc1_ucm_extend_mode                  1
% 3.03/0.98  --bmc1_ucm_init_mode                    2
% 3.03/0.98  --bmc1_ucm_cone_mode                    none
% 3.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.98  --bmc1_ucm_relax_model                  4
% 3.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.98  --bmc1_ucm_layered_model                none
% 3.03/0.98  --bmc1_ucm_max_lemma_size               10
% 3.03/0.98  
% 3.03/0.98  ------ AIG Options
% 3.03/0.98  
% 3.03/0.98  --aig_mode                              false
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation Options
% 3.03/0.98  
% 3.03/0.98  --instantiation_flag                    true
% 3.03/0.98  --inst_sos_flag                         false
% 3.03/0.98  --inst_sos_phase                        true
% 3.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel_side                     none
% 3.03/0.98  --inst_solver_per_active                1400
% 3.03/0.98  --inst_solver_calls_frac                1.
% 3.03/0.98  --inst_passive_queue_type               priority_queues
% 3.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.98  --inst_passive_queues_freq              [25;2]
% 3.03/0.98  --inst_dismatching                      true
% 3.03/0.98  --inst_eager_unprocessed_to_passive     true
% 3.03/0.98  --inst_prop_sim_given                   true
% 3.03/0.98  --inst_prop_sim_new                     false
% 3.03/0.98  --inst_subs_new                         false
% 3.03/0.98  --inst_eq_res_simp                      false
% 3.03/0.98  --inst_subs_given                       false
% 3.03/0.98  --inst_orphan_elimination               true
% 3.03/0.98  --inst_learning_loop_flag               true
% 3.03/0.98  --inst_learning_start                   3000
% 3.03/0.98  --inst_learning_factor                  2
% 3.03/0.98  --inst_start_prop_sim_after_learn       3
% 3.03/0.98  --inst_sel_renew                        solver
% 3.03/0.98  --inst_lit_activity_flag                true
% 3.03/0.98  --inst_restr_to_given                   false
% 3.03/0.98  --inst_activity_threshold               500
% 3.03/0.98  --inst_out_proof                        true
% 3.03/0.98  
% 3.03/0.98  ------ Resolution Options
% 3.03/0.98  
% 3.03/0.98  --resolution_flag                       false
% 3.03/0.98  --res_lit_sel                           adaptive
% 3.03/0.98  --res_lit_sel_side                      none
% 3.03/0.98  --res_ordering                          kbo
% 3.03/0.98  --res_to_prop_solver                    active
% 3.03/0.98  --res_prop_simpl_new                    false
% 3.03/0.98  --res_prop_simpl_given                  true
% 3.03/0.98  --res_passive_queue_type                priority_queues
% 3.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.98  --res_passive_queues_freq               [15;5]
% 3.03/0.98  --res_forward_subs                      full
% 3.03/0.98  --res_backward_subs                     full
% 3.03/0.98  --res_forward_subs_resolution           true
% 3.03/0.98  --res_backward_subs_resolution          true
% 3.03/0.98  --res_orphan_elimination                true
% 3.03/0.98  --res_time_limit                        2.
% 3.03/0.98  --res_out_proof                         true
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Options
% 3.03/0.98  
% 3.03/0.98  --superposition_flag                    true
% 3.03/0.98  --sup_passive_queue_type                priority_queues
% 3.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.98  --demod_completeness_check              fast
% 3.03/0.98  --demod_use_ground                      true
% 3.03/0.98  --sup_to_prop_solver                    passive
% 3.03/0.98  --sup_prop_simpl_new                    true
% 3.03/0.98  --sup_prop_simpl_given                  true
% 3.03/0.98  --sup_fun_splitting                     false
% 3.03/0.98  --sup_smt_interval                      50000
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Simplification Setup
% 3.03/0.98  
% 3.03/0.98  --sup_indices_passive                   []
% 3.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_full_bw                           [BwDemod]
% 3.03/0.98  --sup_immed_triv                        [TrivRules]
% 3.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_immed_bw_main                     []
% 3.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  
% 3.03/0.98  ------ Combination Options
% 3.03/0.98  
% 3.03/0.98  --comb_res_mult                         3
% 3.03/0.98  --comb_sup_mult                         2
% 3.03/0.98  --comb_inst_mult                        10
% 3.03/0.98  
% 3.03/0.98  ------ Debug Options
% 3.03/0.98  
% 3.03/0.98  --dbg_backtrace                         false
% 3.03/0.98  --dbg_dump_prop_clauses                 false
% 3.03/0.98  --dbg_dump_prop_clauses_file            -
% 3.03/0.98  --dbg_out_stat                          false
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ Proving...
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  % SZS status Theorem for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  fof(f19,conjecture,(
% 3.03/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f20,negated_conjecture,(
% 3.03/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.03/0.98    inference(negated_conjecture,[],[f19])).
% 3.03/0.98  
% 3.03/0.98  fof(f43,plain,(
% 3.03/0.98    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.03/0.98    inference(ennf_transformation,[],[f20])).
% 3.03/0.98  
% 3.03/0.98  fof(f44,plain,(
% 3.03/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.03/0.98    inference(flattening,[],[f43])).
% 3.03/0.98  
% 3.03/0.98  fof(f50,plain,(
% 3.03/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f51,plain,(
% 3.03/0.98    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f50])).
% 3.03/0.98  
% 3.03/0.98  fof(f87,plain,(
% 3.03/0.98    r1_tarski(sK1,sK0)),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f86,plain,(
% 3.03/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f11,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f31,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f11])).
% 3.03/0.98  
% 3.03/0.98  fof(f68,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f31])).
% 3.03/0.98  
% 3.03/0.98  fof(f9,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f29,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f9])).
% 3.03/0.98  
% 3.03/0.98  fof(f66,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f29])).
% 3.03/0.98  
% 3.03/0.98  fof(f16,axiom,(
% 3.03/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f37,plain,(
% 3.03/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.03/0.98    inference(ennf_transformation,[],[f16])).
% 3.03/0.98  
% 3.03/0.98  fof(f38,plain,(
% 3.03/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(flattening,[],[f37])).
% 3.03/0.98  
% 3.03/0.98  fof(f49,plain,(
% 3.03/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(nnf_transformation,[],[f38])).
% 3.03/0.98  
% 3.03/0.98  fof(f76,plain,(
% 3.03/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f49])).
% 3.03/0.98  
% 3.03/0.98  fof(f8,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f28,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f8])).
% 3.03/0.98  
% 3.03/0.98  fof(f64,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f28])).
% 3.03/0.98  
% 3.03/0.98  fof(f15,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f35,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f15])).
% 3.03/0.98  
% 3.03/0.98  fof(f36,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(flattening,[],[f35])).
% 3.03/0.98  
% 3.03/0.98  fof(f75,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f36])).
% 3.03/0.98  
% 3.03/0.98  fof(f85,plain,(
% 3.03/0.98    v3_funct_2(sK2,sK0,sK0)),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f83,plain,(
% 3.03/0.98    v1_funct_1(sK2)),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f84,plain,(
% 3.03/0.98    v1_funct_2(sK2,sK0,sK0)),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f18,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f41,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.03/0.98    inference(ennf_transformation,[],[f18])).
% 3.03/0.98  
% 3.03/0.98  fof(f42,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.03/0.98    inference(flattening,[],[f41])).
% 3.03/0.98  
% 3.03/0.98  fof(f81,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f42])).
% 3.03/0.98  
% 3.03/0.98  fof(f14,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f34,plain,(
% 3.03/0.98    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.03/0.98    inference(ennf_transformation,[],[f14])).
% 3.03/0.98  
% 3.03/0.98  fof(f71,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f34])).
% 3.03/0.98  
% 3.03/0.98  fof(f12,axiom,(
% 3.03/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f32,plain,(
% 3.03/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f12])).
% 3.03/0.98  
% 3.03/0.98  fof(f69,plain,(
% 3.03/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f32])).
% 3.03/0.98  
% 3.03/0.98  fof(f72,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f34])).
% 3.03/0.98  
% 3.03/0.98  fof(f10,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f30,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f10])).
% 3.03/0.98  
% 3.03/0.98  fof(f67,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f30])).
% 3.03/0.98  
% 3.03/0.98  fof(f13,axiom,(
% 3.03/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f33,plain,(
% 3.03/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.98    inference(ennf_transformation,[],[f13])).
% 3.03/0.98  
% 3.03/0.98  fof(f70,plain,(
% 3.03/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f33])).
% 3.03/0.98  
% 3.03/0.98  fof(f2,axiom,(
% 3.03/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f55,plain,(
% 3.03/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f2])).
% 3.03/0.98  
% 3.03/0.98  fof(f65,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f29])).
% 3.03/0.98  
% 3.03/0.98  fof(f4,axiom,(
% 3.03/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f21,plain,(
% 3.03/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(ennf_transformation,[],[f4])).
% 3.03/0.98  
% 3.03/0.98  fof(f48,plain,(
% 3.03/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(nnf_transformation,[],[f21])).
% 3.03/0.98  
% 3.03/0.98  fof(f58,plain,(
% 3.03/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f48])).
% 3.03/0.98  
% 3.03/0.98  fof(f1,axiom,(
% 3.03/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f45,plain,(
% 3.03/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.98    inference(nnf_transformation,[],[f1])).
% 3.03/0.98  
% 3.03/0.98  fof(f46,plain,(
% 3.03/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.98    inference(flattening,[],[f45])).
% 3.03/0.98  
% 3.03/0.98  fof(f54,plain,(
% 3.03/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f46])).
% 3.03/0.98  
% 3.03/0.98  fof(f7,axiom,(
% 3.03/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f26,plain,(
% 3.03/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.03/0.98    inference(ennf_transformation,[],[f7])).
% 3.03/0.98  
% 3.03/0.98  fof(f27,plain,(
% 3.03/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(flattening,[],[f26])).
% 3.03/0.98  
% 3.03/0.98  fof(f63,plain,(
% 3.03/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f27])).
% 3.03/0.98  
% 3.03/0.98  fof(f74,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f36])).
% 3.03/0.98  
% 3.03/0.98  fof(f88,plain,(
% 3.03/0.98    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.03/0.98    inference(cnf_transformation,[],[f51])).
% 3.03/0.98  
% 3.03/0.98  fof(f6,axiom,(
% 3.03/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f24,plain,(
% 3.03/0.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.03/0.98    inference(ennf_transformation,[],[f6])).
% 3.03/0.98  
% 3.03/0.98  fof(f25,plain,(
% 3.03/0.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.03/0.98    inference(flattening,[],[f24])).
% 3.03/0.98  
% 3.03/0.98  fof(f62,plain,(
% 3.03/0.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f25])).
% 3.03/0.98  
% 3.03/0.98  cnf(c_32,negated_conjecture,
% 3.03/0.98      ( r1_tarski(sK1,sK0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2662,plain,
% 3.03/0.98      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_33,negated_conjecture,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.03/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2661,plain,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_16,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2667,plain,
% 3.03/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3707,plain,
% 3.03/0.98      ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2667]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_13,plain,
% 3.03/0.98      ( v5_relat_1(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.03/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_25,plain,
% 3.03/0.98      ( ~ v2_funct_2(X0,X1)
% 3.03/0.98      | ~ v5_relat_1(X0,X1)
% 3.03/0.98      | ~ v1_relat_1(X0)
% 3.03/0.98      | k2_relat_1(X0) = X1 ),
% 3.03/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_529,plain,
% 3.03/0.98      ( ~ v2_funct_2(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.03/0.98      | ~ v1_relat_1(X0)
% 3.03/0.98      | k2_relat_1(X0) = X1 ),
% 3.03/0.98      inference(resolution,[status(thm)],[c_13,c_25]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_12,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | v1_relat_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_541,plain,
% 3.03/0.98      ( ~ v2_funct_2(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.03/0.98      | k2_relat_1(X0) = X1 ),
% 3.03/0.98      inference(forward_subsumption_resolution,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_529,c_12]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_21,plain,
% 3.03/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/0.98      | v2_funct_2(X0,X2)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | ~ v1_funct_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_34,negated_conjecture,
% 3.03/0.98      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_468,plain,
% 3.03/0.98      ( v2_funct_2(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.03/0.98      | ~ v1_funct_1(X0)
% 3.03/0.98      | sK2 != X0
% 3.03/0.98      | sK0 != X1
% 3.03/0.98      | sK0 != X2 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_469,plain,
% 3.03/0.98      ( v2_funct_2(sK2,sK0)
% 3.03/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | ~ v1_funct_1(sK2) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_468]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_36,negated_conjecture,
% 3.03/0.98      ( v1_funct_1(sK2) ),
% 3.03/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_471,plain,
% 3.03/0.98      ( v2_funct_2(sK2,sK0) ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_469,c_36,c_33]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_574,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k2_relat_1(X0) = X2
% 3.03/0.98      | sK2 != X0
% 3.03/0.98      | sK0 != X2 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_541,c_471]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_575,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.03/0.98      | k2_relat_1(sK2) = sK0 ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_574]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_577,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | k2_relat_1(sK2) = sK0 ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_575]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_579,plain,
% 3.03/0.98      ( k2_relat_1(sK2) = sK0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_575,c_33,c_577]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3713,plain,
% 3.03/0.98      ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.03/0.98      inference(light_normalisation,[status(thm)],[c_3707,c_579]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_35,negated_conjecture,
% 3.03/0.98      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_30,plain,
% 3.03/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | ~ v1_funct_1(X0)
% 3.03/0.98      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.03/0.98      | k1_xboole_0 = X2 ),
% 3.03/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_600,plain,
% 3.03/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.03/0.98      | sK2 != X0
% 3.03/0.98      | k1_xboole_0 = X2 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_601,plain,
% 3.03/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 3.03/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/0.98      | k8_relset_1(X0,X1,sK2,X1) = X0
% 3.03/0.98      | k1_xboole_0 = X1 ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_600]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_672,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/0.98      | k8_relset_1(X0,X1,sK2,X1) = X0
% 3.03/0.98      | sK2 != sK2
% 3.03/0.98      | sK0 != X1
% 3.03/0.98      | sK0 != X0
% 3.03/0.98      | k1_xboole_0 = X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_35,c_601]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_673,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | k8_relset_1(sK0,sK0,sK2,sK0) = sK0
% 3.03/0.98      | k1_xboole_0 = sK0 ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_672]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_603,plain,
% 3.03/0.98      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.03/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | k8_relset_1(sK0,sK0,sK2,sK0) = sK0
% 3.03/0.98      | k1_xboole_0 = sK0 ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_601]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_675,plain,
% 3.03/0.98      ( k8_relset_1(sK0,sK0,sK2,sK0) = sK0 | k1_xboole_0 = sK0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_673,c_35,c_33,c_603]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_20,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2663,plain,
% 3.03/0.98      ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3486,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK0)) = k2_relset_1(sK0,sK0,sK2) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2663]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3792,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2)
% 3.03/0.98      | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_675,c_3486]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3877,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,sK0) = sK0 | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_3713,c_3792]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_17,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.03/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2666,plain,
% 3.03/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4385,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2666]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4571,plain,
% 3.03/0.98      ( k9_relat_1(sK2,sK0) = sK0 | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_3877,c_4385]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_19,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2664,plain,
% 3.03/0.98      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4141,plain,
% 3.03/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relset_1(sK0,sK0,sK2) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2664]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_15,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2668,plain,
% 3.03/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4241,plain,
% 3.03/0.98      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2668]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4631,plain,
% 3.03/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relat_1(sK2) ),
% 3.03/0.98      inference(light_normalisation,[status(thm)],[c_4141,c_4241]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_18,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.03/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2665,plain,
% 3.03/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.03/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4366,plain,
% 3.03/0.98      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2665]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4632,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k1_relat_1(sK2) ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_4631,c_4366,c_4385]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5143,plain,
% 3.03/0.98      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_4571,c_4632]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4514,plain,
% 3.03/0.98      ( k10_relat_1(sK2,sK0) = sK0 | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_675,c_4366]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5847,plain,
% 3.03/0.98      ( k1_relat_1(sK2) = sK0 | sK0 = k1_xboole_0 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_5143,c_4514]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3,plain,
% 3.03/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3117,plain,
% 3.03/0.98      ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3120,plain,
% 3.03/0.98      ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_3117]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2106,plain,( X0 = X0 ),theory(equality) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3219,plain,
% 3.03/0.98      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_2106]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_14,plain,
% 3.03/0.98      ( v4_relat_1(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.03/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_7,plain,
% 3.03/0.98      ( ~ v4_relat_1(X0,X1)
% 3.03/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.03/0.98      | ~ v1_relat_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_508,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.03/0.98      | ~ v1_relat_1(X0) ),
% 3.03/0.98      inference(resolution,[status(thm)],[c_14,c_7]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_512,plain,
% 3.03/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_508,c_12]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_513,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.03/0.98      inference(renaming,[status(thm)],[c_512]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2659,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2979,plain,
% 3.03/0.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2661,c_2659]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_0,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.03/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2676,plain,
% 3.03/0.98      ( X0 = X1
% 3.03/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.03/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4262,plain,
% 3.03/0.98      ( k1_relat_1(sK2) = sK0
% 3.03/0.98      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2979,c_2676]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2108,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.03/0.98      theory(equality) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3122,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,X1)
% 3.03/0.98      | r1_tarski(X2,k1_relat_1(sK2))
% 3.03/0.98      | X2 != X0
% 3.03/0.98      | k1_relat_1(sK2) != X1 ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_2108]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3634,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.03/0.98      | r1_tarski(X1,k1_relat_1(sK2))
% 3.03/0.98      | X1 != X0
% 3.03/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_3122]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4718,plain,
% 3.03/0.98      ( r1_tarski(X0,k1_relat_1(sK2))
% 3.03/0.98      | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
% 3.03/0.98      | X0 != k1_xboole_0
% 3.03/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_3634]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4719,plain,
% 3.03/0.98      ( X0 != k1_xboole_0
% 3.03/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 3.03/0.98      | r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
% 3.03/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_4718]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4721,plain,
% 3.03/0.98      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 3.03/0.98      | sK0 != k1_xboole_0
% 3.03/0.98      | r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.03/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_4719]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5857,plain,
% 3.03/0.98      ( k1_relat_1(sK2) = sK0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_5847,c_3120,c_3219,c_4262,c_4721]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_11,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.03/0.98      | ~ v2_funct_1(X1)
% 3.03/0.98      | ~ v1_funct_1(X1)
% 3.03/0.98      | ~ v1_relat_1(X1)
% 3.03/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.03/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_22,plain,
% 3.03/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | v2_funct_1(X0)
% 3.03/0.98      | ~ v1_funct_1(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_457,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.98      | v2_funct_1(X0)
% 3.03/0.98      | ~ v1_funct_1(X0)
% 3.03/0.98      | sK2 != X0
% 3.03/0.98      | sK0 != X2
% 3.03/0.98      | sK0 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_458,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | v2_funct_1(sK2)
% 3.03/0.98      | ~ v1_funct_1(sK2) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_457]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_460,plain,
% 3.03/0.98      ( v2_funct_1(sK2) ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_458,c_36,c_33]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_483,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.03/0.98      | ~ v1_funct_1(X1)
% 3.03/0.98      | ~ v1_relat_1(X1)
% 3.03/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.03/0.98      | sK2 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_460]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_484,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.03/0.98      | ~ v1_funct_1(sK2)
% 3.03/0.98      | ~ v1_relat_1(sK2)
% 3.03/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_488,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.03/0.98      | ~ v1_relat_1(sK2)
% 3.03/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_484,c_36]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2660,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.03/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_40,plain,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_490,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.03/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2850,plain,
% 3.03/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/0.98      | v1_relat_1(sK2) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2851,plain,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.03/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_2850]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3395,plain,
% 3.03/0.98      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.03/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_2660,c_40,c_490,c_2851]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3396,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 3.03/0.98      inference(renaming,[status(thm)],[c_3395]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5872,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,sK0) != iProver_top ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_5857,c_3396]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_6476,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2662,c_5872]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_31,negated_conjecture,
% 3.03/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.03/0.98      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.03/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4505,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.03/0.98      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_4366,c_31]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4511,plain,
% 3.03/0.98      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.03/0.98      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_4505,c_4366]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_10,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.03/0.98      | ~ v1_funct_1(X1)
% 3.03/0.98      | ~ v1_relat_1(X1)
% 3.03/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.03/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_585,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.03/0.98      | ~ v1_relat_1(X1)
% 3.03/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 3.03/0.98      | sK2 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_36]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_586,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 3.03/0.98      | ~ v1_relat_1(sK2)
% 3.03/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_585]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2658,plain,
% 3.03/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 3.03/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2744,plain,
% 3.03/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,sK0) != iProver_top
% 3.03/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.98      inference(light_normalisation,[status(thm)],[c_2658,c_579]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2947,plain,
% 3.03/0.98      ( r1_tarski(X0,sK0) != iProver_top
% 3.03/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_2744,c_40,c_2851]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2948,plain,
% 3.03/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.03/0.98      | r1_tarski(X0,sK0) != iProver_top ),
% 3.03/0.98      inference(renaming,[status(thm)],[c_2947]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2955,plain,
% 3.03/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_2662,c_2948]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4634,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 | sK1 != sK1 ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_4511,c_2955,c_4385]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4635,plain,
% 3.03/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
% 3.03/0.98      inference(equality_resolution_simp,[status(thm)],[c_4634]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(contradiction,plain,
% 3.03/0.98      ( $false ),
% 3.03/0.98      inference(minisat,[status(thm)],[c_6476,c_4635]) ).
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  ------                               Statistics
% 3.03/0.98  
% 3.03/0.98  ------ General
% 3.03/0.98  
% 3.03/0.98  abstr_ref_over_cycles:                  0
% 3.03/0.98  abstr_ref_under_cycles:                 0
% 3.03/0.98  gc_basic_clause_elim:                   0
% 3.03/0.98  forced_gc_time:                         0
% 3.03/0.98  parsing_time:                           0.012
% 3.03/0.98  unif_index_cands_time:                  0.
% 3.03/0.98  unif_index_add_time:                    0.
% 3.03/0.98  orderings_time:                         0.
% 3.03/0.98  out_proof_time:                         0.01
% 3.03/0.98  total_time:                             0.188
% 3.03/0.98  num_of_symbols:                         55
% 3.03/0.98  num_of_terms:                           4174
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing
% 3.03/0.98  
% 3.03/0.98  num_of_splits:                          0
% 3.03/0.98  num_of_split_atoms:                     0
% 3.03/0.98  num_of_reused_defs:                     0
% 3.03/0.98  num_eq_ax_congr_red:                    28
% 3.03/0.98  num_of_sem_filtered_clauses:            1
% 3.03/0.98  num_of_subtypes:                        0
% 3.03/0.98  monotx_restored_types:                  0
% 3.03/0.98  sat_num_of_epr_types:                   0
% 3.03/0.98  sat_num_of_non_cyclic_types:            0
% 3.03/0.98  sat_guarded_non_collapsed_types:        0
% 3.03/0.98  num_pure_diseq_elim:                    0
% 3.03/0.98  simp_replaced_by:                       0
% 3.03/0.98  res_preprocessed:                       139
% 3.03/0.98  prep_upred:                             0
% 3.03/0.98  prep_unflattend:                        90
% 3.03/0.98  smt_new_axioms:                         0
% 3.03/0.98  pred_elim_cands:                        3
% 3.03/0.98  pred_elim:                              7
% 3.03/0.98  pred_elim_cl:                           8
% 3.03/0.98  pred_elim_cycles:                       12
% 3.03/0.98  merged_defs:                            8
% 3.03/0.98  merged_defs_ncl:                        0
% 3.03/0.98  bin_hyper_res:                          8
% 3.03/0.98  prep_cycles:                            4
% 3.03/0.98  pred_elim_time:                         0.027
% 3.03/0.98  splitting_time:                         0.
% 3.03/0.98  sem_filter_time:                        0.
% 3.03/0.98  monotx_time:                            0.
% 3.03/0.98  subtype_inf_time:                       0.
% 3.03/0.98  
% 3.03/0.98  ------ Problem properties
% 3.03/0.98  
% 3.03/0.98  clauses:                                26
% 3.03/0.98  conjectures:                            3
% 3.03/0.98  epr:                                    4
% 3.03/0.98  horn:                                   24
% 3.03/0.98  ground:                                 9
% 3.03/0.98  unary:                                  6
% 3.03/0.98  binary:                                 12
% 3.03/0.98  lits:                                   54
% 3.03/0.98  lits_eq:                                24
% 3.03/0.98  fd_pure:                                0
% 3.03/0.98  fd_pseudo:                              0
% 3.03/0.98  fd_cond:                                2
% 3.03/0.98  fd_pseudo_cond:                         1
% 3.03/0.98  ac_symbols:                             0
% 3.03/0.98  
% 3.03/0.98  ------ Propositional Solver
% 3.03/0.98  
% 3.03/0.98  prop_solver_calls:                      28
% 3.03/0.98  prop_fast_solver_calls:                 1081
% 3.03/0.98  smt_solver_calls:                       0
% 3.03/0.98  smt_fast_solver_calls:                  0
% 3.03/0.98  prop_num_of_clauses:                    2024
% 3.03/0.98  prop_preprocess_simplified:             6061
% 3.03/0.98  prop_fo_subsumed:                       18
% 3.03/0.98  prop_solver_time:                       0.
% 3.03/0.98  smt_solver_time:                        0.
% 3.03/0.98  smt_fast_solver_time:                   0.
% 3.03/0.98  prop_fast_solver_time:                  0.
% 3.03/0.98  prop_unsat_core_time:                   0.
% 3.03/0.98  
% 3.03/0.98  ------ QBF
% 3.03/0.98  
% 3.03/0.98  qbf_q_res:                              0
% 3.03/0.98  qbf_num_tautologies:                    0
% 3.03/0.98  qbf_prep_cycles:                        0
% 3.03/0.98  
% 3.03/0.98  ------ BMC1
% 3.03/0.98  
% 3.03/0.98  bmc1_current_bound:                     -1
% 3.03/0.98  bmc1_last_solved_bound:                 -1
% 3.03/0.98  bmc1_unsat_core_size:                   -1
% 3.03/0.98  bmc1_unsat_core_parents_size:           -1
% 3.03/0.98  bmc1_merge_next_fun:                    0
% 3.03/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation
% 3.03/0.98  
% 3.03/0.98  inst_num_of_clauses:                    556
% 3.03/0.98  inst_num_in_passive:                    32
% 3.03/0.98  inst_num_in_active:                     317
% 3.03/0.98  inst_num_in_unprocessed:                210
% 3.03/0.98  inst_num_of_loops:                      390
% 3.03/0.98  inst_num_of_learning_restarts:          0
% 3.03/0.98  inst_num_moves_active_passive:          70
% 3.03/0.98  inst_lit_activity:                      0
% 3.03/0.98  inst_lit_activity_moves:                0
% 3.03/0.98  inst_num_tautologies:                   0
% 3.03/0.98  inst_num_prop_implied:                  0
% 3.03/0.98  inst_num_existing_simplified:           0
% 3.03/0.98  inst_num_eq_res_simplified:             0
% 3.03/0.98  inst_num_child_elim:                    0
% 3.03/0.98  inst_num_of_dismatching_blockings:      249
% 3.03/0.98  inst_num_of_non_proper_insts:           779
% 3.03/0.98  inst_num_of_duplicates:                 0
% 3.03/0.98  inst_inst_num_from_inst_to_res:         0
% 3.03/0.98  inst_dismatching_checking_time:         0.
% 3.03/0.98  
% 3.03/0.98  ------ Resolution
% 3.03/0.98  
% 3.03/0.98  res_num_of_clauses:                     0
% 3.03/0.98  res_num_in_passive:                     0
% 3.03/0.98  res_num_in_active:                      0
% 3.03/0.98  res_num_of_loops:                       143
% 3.03/0.98  res_forward_subset_subsumed:            33
% 3.03/0.98  res_backward_subset_subsumed:           11
% 3.03/0.98  res_forward_subsumed:                   0
% 3.03/0.98  res_backward_subsumed:                  0
% 3.03/0.98  res_forward_subsumption_resolution:     3
% 3.03/0.98  res_backward_subsumption_resolution:    0
% 3.03/0.98  res_clause_to_clause_subsumption:       241
% 3.03/0.98  res_orphan_elimination:                 0
% 3.03/0.98  res_tautology_del:                      70
% 3.03/0.98  res_num_eq_res_simplified:              0
% 3.03/0.98  res_num_sel_changes:                    0
% 3.03/0.98  res_moves_from_active_to_pass:          0
% 3.03/0.98  
% 3.03/0.98  ------ Superposition
% 3.03/0.98  
% 3.03/0.98  sup_time_total:                         0.
% 3.03/0.98  sup_time_generating:                    0.
% 3.03/0.98  sup_time_sim_full:                      0.
% 3.03/0.98  sup_time_sim_immed:                     0.
% 3.03/0.98  
% 3.03/0.98  sup_num_of_clauses:                     78
% 3.03/0.98  sup_num_in_active:                      56
% 3.03/0.98  sup_num_in_passive:                     22
% 3.03/0.98  sup_num_of_loops:                       76
% 3.03/0.98  sup_fw_superposition:                   71
% 3.03/0.98  sup_bw_superposition:                   23
% 3.03/0.98  sup_immediate_simplified:               6
% 3.03/0.98  sup_given_eliminated:                   0
% 3.03/0.98  comparisons_done:                       0
% 3.03/0.98  comparisons_avoided:                    9
% 3.03/0.98  
% 3.03/0.98  ------ Simplifications
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  sim_fw_subset_subsumed:                 0
% 3.03/0.98  sim_bw_subset_subsumed:                 1
% 3.03/0.98  sim_fw_subsumed:                        2
% 3.03/0.98  sim_bw_subsumed:                        0
% 3.03/0.98  sim_fw_subsumption_res:                 0
% 3.03/0.98  sim_bw_subsumption_res:                 0
% 3.03/0.98  sim_tautology_del:                      1
% 3.03/0.98  sim_eq_tautology_del:                   4
% 3.03/0.98  sim_eq_res_simp:                        1
% 3.03/0.98  sim_fw_demodulated:                     8
% 3.03/0.98  sim_bw_demodulated:                     20
% 3.03/0.98  sim_light_normalised:                   10
% 3.03/0.98  sim_joinable_taut:                      0
% 3.03/0.98  sim_joinable_simp:                      0
% 3.03/0.98  sim_ac_normalised:                      0
% 3.03/0.98  sim_smt_subsumption:                    0
% 3.03/0.98  
%------------------------------------------------------------------------------
