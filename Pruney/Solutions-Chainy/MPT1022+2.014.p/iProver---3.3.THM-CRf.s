%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:38 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  177 (1889 expanded)
%              Number of clauses        :  110 ( 688 expanded)
%              Number of leaves         :   17 ( 349 expanded)
%              Depth                    :   31
%              Number of atoms          :  515 (8531 expanded)
%              Number of equality atoms :  240 (2569 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f48])).

fof(f85,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1805,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1804,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1811,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2721,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1811])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_325,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_259])).

cnf(c_1803,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_3343,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2721,c_1803])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1810,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3809,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3343,c_1810])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_20,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_467,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_468,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_470,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_36,c_33])).

cnf(c_567,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_470])).

cnf(c_568,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_568])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_1286,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK2) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_585])).

cnf(c_1798,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_1318,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_1285,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_585])).

cnf(c_1799,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1285])).

cnf(c_2038,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1799])).

cnf(c_2116,plain,
    ( v1_relat_1(sK2) != iProver_top
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_1318,c_2038])).

cnf(c_2117,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2116])).

cnf(c_3818,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_3809,c_2117])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_507,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_508,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1800,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_5159,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3818,c_1800])).

cnf(c_5323,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5159,c_3809])).

cnf(c_5324,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5323])).

cnf(c_5331,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1805,c_5324])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1807,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4106,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1804,c_1807])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1806,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3548,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1804,c_1806])).

cnf(c_31,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3632,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_3548,c_31])).

cnf(c_3633,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_3632,c_3548])).

cnf(c_4279,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_4106,c_3633])).

cnf(c_4280,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_4279,c_4106])).

cnf(c_5336,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_5331,c_4280])).

cnf(c_5337,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_5336])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_651,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_33])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1808,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2867,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1804,c_1808])).

cnf(c_2984,plain,
    ( k1_relat_1(sK2) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_651,c_2867])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_457,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_459,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_36,c_33])).

cnf(c_482,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_459])).

cnf(c_483,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_36])).

cnf(c_1801,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3105,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | sK0 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_1801])).

cnf(c_3114,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | sK0 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3105])).

cnf(c_3812,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3809,c_3114])).

cnf(c_4436,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3812,c_4280])).

cnf(c_5335,plain,
    ( sK1 != sK1
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5331,c_4436])).

cnf(c_5340,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5335])).

cnf(c_5421,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5340,c_1805])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1813,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1815,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3473,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1815])).

cnf(c_5476,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5421,c_3473])).

cnf(c_5416,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5340,c_2721])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5433,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5416,c_5])).

cnf(c_5933,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5433,c_3473])).

cnf(c_6460,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5337,c_5476,c_5933])).

cnf(c_6084,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5933,c_1801])).

cnf(c_6100,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6084])).

cnf(c_2310,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2313,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_2315,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_2076,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2079,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_1964,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_2075,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_2077,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_100,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6462,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_2079:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_6463,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_2077:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_6464,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_100:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6460,c_6100,c_2315,c_6462,c_6463,c_6464])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.13/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.01  
% 3.13/1.01  ------  iProver source info
% 3.13/1.01  
% 3.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.01  git: non_committed_changes: false
% 3.13/1.01  git: last_make_outside_of_git: false
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     num_symb
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       true
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  ------ Parsing...
% 3.13/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.01  ------ Proving...
% 3.13/1.01  ------ Problem Properties 
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  clauses                                 25
% 3.13/1.01  conjectures                             3
% 3.13/1.01  EPR                                     5
% 3.13/1.01  Horn                                    21
% 3.13/1.01  unary                                   7
% 3.13/1.01  binary                                  8
% 3.13/1.01  lits                                    54
% 3.13/1.01  lits eq                                 23
% 3.13/1.01  fd_pure                                 0
% 3.13/1.01  fd_pseudo                               0
% 3.13/1.01  fd_cond                                 1
% 3.13/1.01  fd_pseudo_cond                          1
% 3.13/1.01  AC symbols                              0
% 3.13/1.01  
% 3.13/1.01  ------ Schedule dynamic 5 is on 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  Current options:
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     none
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       false
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ Proving...
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS status Theorem for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  fof(f18,conjecture,(
% 3.13/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f19,negated_conjecture,(
% 3.13/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.13/1.01    inference(negated_conjecture,[],[f18])).
% 3.13/1.01  
% 3.13/1.01  fof(f39,plain,(
% 3.13/1.01    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.13/1.01    inference(ennf_transformation,[],[f19])).
% 3.13/1.01  
% 3.13/1.01  fof(f40,plain,(
% 3.13/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.13/1.01    inference(flattening,[],[f39])).
% 3.13/1.01  
% 3.13/1.01  fof(f48,plain,(
% 3.13/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f49,plain,(
% 3.13/1.01    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f48])).
% 3.13/1.01  
% 3.13/1.01  fof(f85,plain,(
% 3.13/1.01    r1_tarski(sK1,sK0)),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f84,plain,(
% 3.13/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f4,axiom,(
% 3.13/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f45,plain,(
% 3.13/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.13/1.01    inference(nnf_transformation,[],[f4])).
% 3.13/1.01  
% 3.13/1.01  fof(f57,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f45])).
% 3.13/1.01  
% 3.13/1.01  fof(f5,axiom,(
% 3.13/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f20,plain,(
% 3.13/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f5])).
% 3.13/1.01  
% 3.13/1.01  fof(f59,plain,(
% 3.13/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f20])).
% 3.13/1.01  
% 3.13/1.01  fof(f58,plain,(
% 3.13/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f45])).
% 3.13/1.01  
% 3.13/1.01  fof(f6,axiom,(
% 3.13/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f60,plain,(
% 3.13/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f6])).
% 3.13/1.01  
% 3.13/1.01  fof(f11,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f29,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f11])).
% 3.13/1.01  
% 3.13/1.01  fof(f66,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f29])).
% 3.13/1.01  
% 3.13/1.01  fof(f17,axiom,(
% 3.13/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f37,plain,(
% 3.13/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.13/1.01    inference(ennf_transformation,[],[f17])).
% 3.13/1.01  
% 3.13/1.01  fof(f38,plain,(
% 3.13/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(flattening,[],[f37])).
% 3.13/1.01  
% 3.13/1.01  fof(f47,plain,(
% 3.13/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(nnf_transformation,[],[f38])).
% 3.13/1.01  
% 3.13/1.01  fof(f79,plain,(
% 3.13/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f47])).
% 3.13/1.01  
% 3.13/1.01  fof(f15,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f33,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f15])).
% 3.13/1.01  
% 3.13/1.01  fof(f34,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(flattening,[],[f33])).
% 3.13/1.01  
% 3.13/1.01  fof(f72,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f34])).
% 3.13/1.01  
% 3.13/1.01  fof(f83,plain,(
% 3.13/1.01    v3_funct_2(sK2,sK0,sK0)),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f81,plain,(
% 3.13/1.01    v1_funct_1(sK2)),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f9,axiom,(
% 3.13/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f25,plain,(
% 3.13/1.01    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.13/1.01    inference(ennf_transformation,[],[f9])).
% 3.13/1.01  
% 3.13/1.01  fof(f26,plain,(
% 3.13/1.01    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(flattening,[],[f25])).
% 3.13/1.01  
% 3.13/1.01  fof(f63,plain,(
% 3.13/1.01    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f26])).
% 3.13/1.01  
% 3.13/1.01  fof(f13,axiom,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f31,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f13])).
% 3.13/1.01  
% 3.13/1.01  fof(f68,plain,(
% 3.13/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f31])).
% 3.13/1.01  
% 3.13/1.01  fof(f14,axiom,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f32,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f14])).
% 3.13/1.01  
% 3.13/1.01  fof(f69,plain,(
% 3.13/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f32])).
% 3.13/1.01  
% 3.13/1.01  fof(f86,plain,(
% 3.13/1.01    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f16,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f35,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f16])).
% 3.13/1.01  
% 3.13/1.01  fof(f36,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(flattening,[],[f35])).
% 3.13/1.01  
% 3.13/1.01  fof(f46,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(nnf_transformation,[],[f36])).
% 3.13/1.01  
% 3.13/1.01  fof(f73,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f46])).
% 3.13/1.01  
% 3.13/1.01  fof(f82,plain,(
% 3.13/1.01    v1_funct_2(sK2,sK0,sK0)),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f12,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f30,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f12])).
% 3.13/1.01  
% 3.13/1.01  fof(f67,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f30])).
% 3.13/1.01  
% 3.13/1.01  fof(f10,axiom,(
% 3.13/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f27,plain,(
% 3.13/1.01    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.13/1.01    inference(ennf_transformation,[],[f10])).
% 3.13/1.01  
% 3.13/1.01  fof(f28,plain,(
% 3.13/1.01    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(flattening,[],[f27])).
% 3.13/1.01  
% 3.13/1.01  fof(f64,plain,(
% 3.13/1.01    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f28])).
% 3.13/1.01  
% 3.13/1.01  fof(f71,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f34])).
% 3.13/1.01  
% 3.13/1.01  fof(f2,axiom,(
% 3.13/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f53,plain,(
% 3.13/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f2])).
% 3.13/1.01  
% 3.13/1.01  fof(f1,axiom,(
% 3.13/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f41,plain,(
% 3.13/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.01    inference(nnf_transformation,[],[f1])).
% 3.13/1.01  
% 3.13/1.01  fof(f42,plain,(
% 3.13/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.01    inference(flattening,[],[f41])).
% 3.13/1.01  
% 3.13/1.01  fof(f52,plain,(
% 3.13/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f42])).
% 3.13/1.01  
% 3.13/1.01  fof(f3,axiom,(
% 3.13/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f43,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/1.01    inference(nnf_transformation,[],[f3])).
% 3.13/1.01  
% 3.13/1.01  fof(f44,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/1.01    inference(flattening,[],[f43])).
% 3.13/1.01  
% 3.13/1.01  fof(f55,plain,(
% 3.13/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.13/1.01    inference(cnf_transformation,[],[f44])).
% 3.13/1.01  
% 3.13/1.01  fof(f90,plain,(
% 3.13/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.13/1.01    inference(equality_resolution,[],[f55])).
% 3.13/1.01  
% 3.13/1.01  cnf(c_32,negated_conjecture,
% 3.13/1.01      ( r1_tarski(sK1,sK0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1805,plain,
% 3.13/1.01      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_33,negated_conjecture,
% 3.13/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1804,plain,
% 3.13/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1811,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.13/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2721,plain,
% 3.13/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1804,c_1811]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | v1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_258,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.13/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_259,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_258]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_325,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.13/1.01      inference(bin_hyper_res,[status(thm)],[c_9,c_259]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1803,plain,
% 3.13/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.13/1.01      | v1_relat_1(X1) != iProver_top
% 3.13/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3343,plain,
% 3.13/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.13/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2721,c_1803]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10,plain,
% 3.13/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1810,plain,
% 3.13/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3809,plain,
% 3.13/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.13/1.01      inference(forward_subsumption_resolution,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_3343,c_1810]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_15,plain,
% 3.13/1.01      ( v5_relat_1(X0,X1)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_30,plain,
% 3.13/1.01      ( ~ v2_funct_2(X0,X1)
% 3.13/1.01      | ~ v5_relat_1(X0,X1)
% 3.13/1.01      | ~ v1_relat_1(X0)
% 3.13/1.01      | k2_relat_1(X0) = X1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_20,plain,
% 3.13/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.13/1.01      | v2_funct_2(X0,X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_funct_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_34,negated_conjecture,
% 3.13/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_467,plain,
% 3.13/1.01      ( v2_funct_2(X0,X1)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | sK2 != X0
% 3.13/1.01      | sK0 != X1
% 3.13/1.01      | sK0 != X2 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_468,plain,
% 3.13/1.01      ( v2_funct_2(sK2,sK0)
% 3.13/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.13/1.01      | ~ v1_funct_1(sK2) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_467]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_36,negated_conjecture,
% 3.13/1.01      ( v1_funct_1(sK2) ),
% 3.13/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_470,plain,
% 3.13/1.01      ( v2_funct_2(sK2,sK0) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_468,c_36,c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_567,plain,
% 3.13/1.01      ( ~ v5_relat_1(X0,X1)
% 3.13/1.01      | ~ v1_relat_1(X0)
% 3.13/1.01      | k2_relat_1(X0) = X1
% 3.13/1.01      | sK2 != X0
% 3.13/1.01      | sK0 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_470]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_568,plain,
% 3.13/1.01      ( ~ v5_relat_1(sK2,sK0)
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_584,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k2_relat_1(sK2) = sK0
% 3.13/1.01      | sK2 != X0
% 3.13/1.01      | sK0 != X2 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_568]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_585,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_584]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1286,plain,
% 3.13/1.01      ( ~ v1_relat_1(sK2) | sP0_iProver_split | k2_relat_1(sK2) = sK0 ),
% 3.13/1.01      inference(splitting,
% 3.13/1.01                [splitting(split),new_symbols(definition,[])],
% 3.13/1.01                [c_585]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1798,plain,
% 3.13/1.01      ( k2_relat_1(sK2) = sK0
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top
% 3.13/1.01      | sP0_iProver_split = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1318,plain,
% 3.13/1.01      ( k2_relat_1(sK2) = sK0
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top
% 3.13/1.01      | sP0_iProver_split = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1285,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.13/1.01      | ~ sP0_iProver_split ),
% 3.13/1.01      inference(splitting,
% 3.13/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.13/1.01                [c_585]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1799,plain,
% 3.13/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.13/1.01      | sP0_iProver_split != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1285]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2038,plain,
% 3.13/1.01      ( sP0_iProver_split != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1804,c_1799]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2116,plain,
% 3.13/1.01      ( v1_relat_1(sK2) != iProver_top | k2_relat_1(sK2) = sK0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_1798,c_1318,c_2038]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2117,plain,
% 3.13/1.01      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_2116]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3818,plain,
% 3.13/1.01      ( k2_relat_1(sK2) = sK0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3809,c_2117]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_13,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.13/1.01      | ~ v1_funct_1(X1)
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_507,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 3.13/1.01      | sK2 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_36]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_508,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_507]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1800,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.13/1.01      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5159,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.13/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_3818,c_1800]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5323,plain,
% 3.13/1.01      ( r1_tarski(X0,sK0) != iProver_top
% 3.13/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_5159,c_3809]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5324,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.13/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_5323]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5331,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1805,c_5324]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_18,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1807,plain,
% 3.13/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4106,plain,
% 3.13/1.01      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1804,c_1807]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_19,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1806,plain,
% 3.13/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3548,plain,
% 3.13/1.01      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1804,c_1806]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_31,negated_conjecture,
% 3.13/1.01      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.13/1.01      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3632,plain,
% 3.13/1.01      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.13/1.01      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_3548,c_31]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3633,plain,
% 3.13/1.01      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.13/1.01      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_3632,c_3548]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4279,plain,
% 3.13/1.01      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.13/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_4106,c_3633]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4280,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.13/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_4279,c_4106]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5336,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 | sK1 != sK1 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5331,c_4280]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5337,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_5336]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_28,plain,
% 3.13/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_35,negated_conjecture,
% 3.13/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_648,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.01      | sK2 != X0
% 3.13/1.01      | sK0 != X2
% 3.13/1.01      | sK0 != X1
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_649,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.13/1.01      | k1_relset_1(sK0,sK0,sK2) = sK0
% 3.13/1.01      | k1_xboole_0 = sK0 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_648]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_651,plain,
% 3.13/1.01      ( k1_relset_1(sK0,sK0,sK2) = sK0 | k1_xboole_0 = sK0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_649,c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_17,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1808,plain,
% 3.13/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2867,plain,
% 3.13/1.01      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1804,c_1808]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2984,plain,
% 3.13/1.01      ( k1_relat_1(sK2) = sK0 | sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_651,c_2867]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_14,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.13/1.01      | ~ v2_funct_1(X1)
% 3.13/1.01      | ~ v1_funct_1(X1)
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_21,plain,
% 3.13/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | v2_funct_1(X0)
% 3.13/1.01      | ~ v1_funct_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_456,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | v2_funct_1(X0)
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | sK2 != X0
% 3.13/1.01      | sK0 != X2
% 3.13/1.01      | sK0 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_457,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.13/1.01      | v2_funct_1(sK2)
% 3.13/1.01      | ~ v1_funct_1(sK2) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_456]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_459,plain,
% 3.13/1.01      ( v2_funct_1(sK2) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_457,c_36,c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_482,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.13/1.01      | ~ v1_funct_1(X1)
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.13/1.01      | sK2 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_459]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_483,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.13/1.01      | ~ v1_funct_1(sK2)
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_482]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_487,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.13/1.01      | ~ v1_relat_1(sK2)
% 3.13/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_483,c_36]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1801,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.13/1.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3105,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.13/1.01      | sK0 = k1_xboole_0
% 3.13/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2984,c_1801]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3114,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 3.13/1.01      | sK0 = k1_xboole_0
% 3.13/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1805,c_3105]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3812,plain,
% 3.13/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 | sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3809,c_3114]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4436,plain,
% 3.13/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 | sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3812,c_4280]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5335,plain,
% 3.13/1.01      ( sK1 != sK1 | sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5331,c_4436]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5340,plain,
% 3.13/1.01      ( sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_5335]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5421,plain,
% 3.13/1.01      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5340,c_1805]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1813,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_0,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1815,plain,
% 3.13/1.01      ( X0 = X1
% 3.13/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.13/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3473,plain,
% 3.13/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1813,c_1815]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5476,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5421,c_3473]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5416,plain,
% 3.13/1.01      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5340,c_2721]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5,plain,
% 3.13/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5433,plain,
% 3.13/1.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5416,c_5]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5933,plain,
% 3.13/1.01      ( sK2 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5433,c_3473]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6460,plain,
% 3.13/1.01      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.13/1.01      inference(light_normalisation,[status(thm)],[c_5337,c_5476,c_5933]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6084,plain,
% 3.13/1.01      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
% 3.13/1.01      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.13/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5933,c_1801]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6100,plain,
% 3.13/1.01      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 3.13/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.13/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_6084]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2310,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2313,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2310]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2315,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2313]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2076,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2079,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1964,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.13/1.01      | v1_relat_1(X0)
% 3.13/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_325]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2075,plain,
% 3.13/1.01      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
% 3.13/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.13/1.01      | v1_relat_1(k1_xboole_0) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1964]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2077,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.13/1.01      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 3.13/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2075]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_100,plain,
% 3.13/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6462,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(grounding,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_2079:[bind(X1,$fot(k1_xboole_0)),
% 3.13/1.01                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6463,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.13/1.01      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.13/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(grounding,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_2077:[bind(X1,$fot(k1_xboole_0)),
% 3.13/1.01                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6464,plain,
% 3.13/1.01      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.13/1.01      inference(grounding,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_100:[bind(X1,$fot(k1_xboole_0)),
% 3.13/1.01                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(contradiction,plain,
% 3.13/1.01      ( $false ),
% 3.13/1.01      inference(minisat,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_6460,c_6100,c_2315,c_6462,c_6463,c_6464]) ).
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  ------                               Statistics
% 3.13/1.01  
% 3.13/1.01  ------ General
% 3.13/1.01  
% 3.13/1.01  abstr_ref_over_cycles:                  0
% 3.13/1.01  abstr_ref_under_cycles:                 0
% 3.13/1.01  gc_basic_clause_elim:                   0
% 3.13/1.01  forced_gc_time:                         0
% 3.13/1.01  parsing_time:                           0.009
% 3.13/1.01  unif_index_cands_time:                  0.
% 3.13/1.01  unif_index_add_time:                    0.
% 3.13/1.01  orderings_time:                         0.
% 3.13/1.01  out_proof_time:                         0.017
% 3.13/1.01  total_time:                             0.238
% 3.13/1.01  num_of_symbols:                         56
% 3.13/1.01  num_of_terms:                           4434
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing
% 3.13/1.01  
% 3.13/1.01  num_of_splits:                          1
% 3.13/1.01  num_of_split_atoms:                     1
% 3.13/1.01  num_of_reused_defs:                     0
% 3.13/1.01  num_eq_ax_congr_red:                    16
% 3.13/1.01  num_of_sem_filtered_clauses:            1
% 3.13/1.01  num_of_subtypes:                        0
% 3.13/1.01  monotx_restored_types:                  0
% 3.13/1.01  sat_num_of_epr_types:                   0
% 3.13/1.01  sat_num_of_non_cyclic_types:            0
% 3.13/1.01  sat_guarded_non_collapsed_types:        0
% 3.13/1.01  num_pure_diseq_elim:                    0
% 3.13/1.01  simp_replaced_by:                       0
% 3.13/1.01  res_preprocessed:                       138
% 3.13/1.01  prep_upred:                             0
% 3.13/1.01  prep_unflattend:                        67
% 3.13/1.01  smt_new_axioms:                         0
% 3.13/1.01  pred_elim_cands:                        3
% 3.13/1.01  pred_elim:                              7
% 3.13/1.01  pred_elim_cl:                           11
% 3.13/1.01  pred_elim_cycles:                       10
% 3.13/1.01  merged_defs:                            8
% 3.13/1.01  merged_defs_ncl:                        0
% 3.13/1.01  bin_hyper_res:                          9
% 3.13/1.01  prep_cycles:                            4
% 3.13/1.01  pred_elim_time:                         0.013
% 3.13/1.01  splitting_time:                         0.
% 3.13/1.01  sem_filter_time:                        0.
% 3.13/1.01  monotx_time:                            0.
% 3.13/1.01  subtype_inf_time:                       0.
% 3.13/1.01  
% 3.13/1.01  ------ Problem properties
% 3.13/1.01  
% 3.13/1.01  clauses:                                25
% 3.13/1.01  conjectures:                            3
% 3.13/1.01  epr:                                    5
% 3.13/1.01  horn:                                   21
% 3.13/1.01  ground:                                 7
% 3.13/1.01  unary:                                  7
% 3.13/1.01  binary:                                 8
% 3.13/1.01  lits:                                   54
% 3.13/1.01  lits_eq:                                23
% 3.13/1.01  fd_pure:                                0
% 3.13/1.01  fd_pseudo:                              0
% 3.13/1.01  fd_cond:                                1
% 3.13/1.01  fd_pseudo_cond:                         1
% 3.13/1.01  ac_symbols:                             0
% 3.13/1.01  
% 3.13/1.01  ------ Propositional Solver
% 3.13/1.01  
% 3.13/1.01  prop_solver_calls:                      29
% 3.13/1.01  prop_fast_solver_calls:                 971
% 3.13/1.01  smt_solver_calls:                       0
% 3.13/1.01  smt_fast_solver_calls:                  0
% 3.13/1.01  prop_num_of_clauses:                    2142
% 3.13/1.01  prop_preprocess_simplified:             5954
% 3.13/1.01  prop_fo_subsumed:                       10
% 3.13/1.01  prop_solver_time:                       0.
% 3.13/1.01  smt_solver_time:                        0.
% 3.13/1.01  smt_fast_solver_time:                   0.
% 3.13/1.01  prop_fast_solver_time:                  0.
% 3.13/1.01  prop_unsat_core_time:                   0.
% 3.13/1.01  
% 3.13/1.01  ------ QBF
% 3.13/1.01  
% 3.13/1.01  qbf_q_res:                              0
% 3.13/1.01  qbf_num_tautologies:                    0
% 3.13/1.01  qbf_prep_cycles:                        0
% 3.13/1.01  
% 3.13/1.01  ------ BMC1
% 3.13/1.01  
% 3.13/1.01  bmc1_current_bound:                     -1
% 3.13/1.01  bmc1_last_solved_bound:                 -1
% 3.13/1.01  bmc1_unsat_core_size:                   -1
% 3.13/1.01  bmc1_unsat_core_parents_size:           -1
% 3.13/1.01  bmc1_merge_next_fun:                    0
% 3.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation
% 3.13/1.01  
% 3.13/1.01  inst_num_of_clauses:                    611
% 3.13/1.01  inst_num_in_passive:                    277
% 3.13/1.01  inst_num_in_active:                     299
% 3.13/1.01  inst_num_in_unprocessed:                35
% 3.13/1.01  inst_num_of_loops:                      420
% 3.13/1.01  inst_num_of_learning_restarts:          0
% 3.13/1.01  inst_num_moves_active_passive:          117
% 3.13/1.01  inst_lit_activity:                      0
% 3.13/1.01  inst_lit_activity_moves:                0
% 3.13/1.01  inst_num_tautologies:                   0
% 3.13/1.01  inst_num_prop_implied:                  0
% 3.13/1.01  inst_num_existing_simplified:           0
% 3.13/1.01  inst_num_eq_res_simplified:             0
% 3.13/1.01  inst_num_child_elim:                    0
% 3.13/1.01  inst_num_of_dismatching_blockings:      228
% 3.13/1.01  inst_num_of_non_proper_insts:           797
% 3.13/1.01  inst_num_of_duplicates:                 0
% 3.13/1.01  inst_inst_num_from_inst_to_res:         0
% 3.13/1.01  inst_dismatching_checking_time:         0.
% 3.13/1.01  
% 3.13/1.01  ------ Resolution
% 3.13/1.01  
% 3.13/1.01  res_num_of_clauses:                     0
% 3.13/1.01  res_num_in_passive:                     0
% 3.13/1.01  res_num_in_active:                      0
% 3.13/1.01  res_num_of_loops:                       142
% 3.13/1.01  res_forward_subset_subsumed:            29
% 3.13/1.01  res_backward_subset_subsumed:           2
% 3.13/1.01  res_forward_subsumed:                   0
% 3.13/1.01  res_backward_subsumed:                  0
% 3.13/1.01  res_forward_subsumption_resolution:     0
% 3.13/1.01  res_backward_subsumption_resolution:    0
% 3.13/1.01  res_clause_to_clause_subsumption:       229
% 3.13/1.01  res_orphan_elimination:                 0
% 3.13/1.01  res_tautology_del:                      84
% 3.13/1.01  res_num_eq_res_simplified:              0
% 3.13/1.01  res_num_sel_changes:                    0
% 3.13/1.01  res_moves_from_active_to_pass:          0
% 3.13/1.01  
% 3.13/1.01  ------ Superposition
% 3.13/1.01  
% 3.13/1.01  sup_time_total:                         0.
% 3.13/1.01  sup_time_generating:                    0.
% 3.13/1.01  sup_time_sim_full:                      0.
% 3.13/1.01  sup_time_sim_immed:                     0.
% 3.13/1.01  
% 3.13/1.01  sup_num_of_clauses:                     81
% 3.13/1.01  sup_num_in_active:                      38
% 3.13/1.01  sup_num_in_passive:                     43
% 3.13/1.01  sup_num_of_loops:                       82
% 3.13/1.01  sup_fw_superposition:                   67
% 3.13/1.01  sup_bw_superposition:                   45
% 3.13/1.01  sup_immediate_simplified:               22
% 3.13/1.01  sup_given_eliminated:                   2
% 3.13/1.01  comparisons_done:                       0
% 3.13/1.01  comparisons_avoided:                    18
% 3.13/1.01  
% 3.13/1.01  ------ Simplifications
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  sim_fw_subset_subsumed:                 7
% 3.13/1.01  sim_bw_subset_subsumed:                 11
% 3.13/1.01  sim_fw_subsumed:                        2
% 3.13/1.01  sim_bw_subsumed:                        1
% 3.13/1.01  sim_fw_subsumption_res:                 2
% 3.13/1.01  sim_bw_subsumption_res:                 0
% 3.13/1.01  sim_tautology_del:                      3
% 3.13/1.01  sim_eq_tautology_del:                   8
% 3.13/1.01  sim_eq_res_simp:                        3
% 3.13/1.01  sim_fw_demodulated:                     7
% 3.13/1.01  sim_bw_demodulated:                     36
% 3.13/1.01  sim_light_normalised:                   16
% 3.13/1.01  sim_joinable_taut:                      0
% 3.13/1.01  sim_joinable_simp:                      0
% 3.13/1.01  sim_ac_normalised:                      0
% 3.13/1.01  sim_smt_subsumption:                    0
% 3.13/1.01  
%------------------------------------------------------------------------------
