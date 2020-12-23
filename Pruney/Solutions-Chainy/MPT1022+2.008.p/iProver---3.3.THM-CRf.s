%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:37 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 665 expanded)
%              Number of clauses        :   79 ( 212 expanded)
%              Number of leaves         :   15 ( 130 expanded)
%              Depth                    :   21
%              Number of atoms          :  431 (3214 expanded)
%              Number of equality atoms :  190 ( 953 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3
        | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3 )
      & r1_tarski(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3
      | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3 )
    & r1_tarski(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f60])).

fof(f102,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,
    ( k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3
    | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1238,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1237,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1241,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1743,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1241])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1744,plain,
    ( ~ v1_funct_2(sK4,sK2,sK2)
    | k1_relset_1(sK2,sK2,sK4) = sK2
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1743])).

cnf(c_2025,plain,
    ( sK2 = k1_xboole_0
    | k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_40,c_1744])).

cnf(c_2026,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2025])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1251,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2693,plain,
    ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1237,c_1251])).

cnf(c_2839,plain,
    ( k1_relat_1(sK4) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2026,c_2693])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1254,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5631,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_1254])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_44,plain,
    ( v3_funct_2(sK4,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1713,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1891,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_1892,plain,
    ( v3_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1891])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1761,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1903,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1761,c_9])).

cnf(c_1904,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_8024,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | sK2 = k1_xboole_0
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5631,c_42,c_44,c_45,c_1892,c_1904])).

cnf(c_8025,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8024])).

cnf(c_8035,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1238,c_8025])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1249,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3331,plain,
    ( k8_relset_1(sK2,sK2,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1237,c_1249])).

cnf(c_36,negated_conjecture,
    ( k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3
    | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3581,plain,
    ( k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3
    | k10_relat_1(sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_3331,c_36])).

cnf(c_3582,plain,
    ( k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) != sK3
    | k10_relat_1(sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_3581,c_3331])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1250,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3336,plain,
    ( k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1237,c_1250])).

cnf(c_3722,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,sK3)) != sK3
    | k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_3582,c_3336])).

cnf(c_25,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1248,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | v2_funct_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5453,plain,
    ( v3_funct_2(sK4,sK2,sK2) != iProver_top
    | v2_funct_2(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1248])).

cnf(c_1733,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | v2_funct_2(sK4,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1939,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | v2_funct_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_1940,plain,
    ( v3_funct_2(sK4,sK2,sK2) != iProver_top
    | v2_funct_2(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1939])).

cnf(c_6324,plain,
    ( v2_funct_2(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5453,c_42,c_44,c_45,c_1940])).

cnf(c_35,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1239,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6329,plain,
    ( k2_relat_1(sK4) = sK2
    | v5_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6324,c_1239])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1650,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1837,plain,
    ( ~ v2_funct_2(sK4,sK2)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6332,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6329,c_41,c_39,c_38,c_1650,c_1837,c_1903,c_1939])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1255,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6358,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6332,c_1255])).

cnf(c_7047,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6358,c_42,c_1904])).

cnf(c_7055,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1238,c_7047])).

cnf(c_8314,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8035,c_3722,c_7055])).

cnf(c_8339,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8314,c_1238])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1266,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1269,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2699,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1269])).

cnf(c_8414,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8339,c_2699])).

cnf(c_7061,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_7055,c_3722])).

cnf(c_7890,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_7061])).

cnf(c_9685,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8414,c_7890])).

cnf(c_2442,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2065,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2067,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9685,c_2442,c_2067,c_1903,c_1891,c_38,c_39,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:58:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.70/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.98  
% 3.70/0.98  ------  iProver source info
% 3.70/0.98  
% 3.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.98  git: non_committed_changes: false
% 3.70/0.98  git: last_make_outside_of_git: false
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  ------ Parsing...
% 3.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  ------ Proving...
% 3.70/0.98  ------ Problem Properties 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  clauses                                 40
% 3.70/0.98  conjectures                             6
% 3.70/0.98  EPR                                     9
% 3.70/0.98  Horn                                    33
% 3.70/0.98  unary                                   8
% 3.70/0.98  binary                                  11
% 3.70/0.98  lits                                    113
% 3.70/0.98  lits eq                                 24
% 3.70/0.98  fd_pure                                 0
% 3.70/0.98  fd_pseudo                               0
% 3.70/0.98  fd_cond                                 3
% 3.70/0.98  fd_pseudo_cond                          5
% 3.70/0.98  AC symbols                              0
% 3.70/0.98  
% 3.70/0.98  ------ Input Options Time Limit: Unbounded
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  Current options:
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS status Theorem for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  fof(f20,conjecture,(
% 3.70/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f21,negated_conjecture,(
% 3.70/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.70/0.98    inference(negated_conjecture,[],[f20])).
% 3.70/0.98  
% 3.70/0.98  fof(f45,plain,(
% 3.70/0.98    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.70/0.98    inference(ennf_transformation,[],[f21])).
% 3.70/0.98  
% 3.70/0.98  fof(f46,plain,(
% 3.70/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.70/0.98    inference(flattening,[],[f45])).
% 3.70/0.98  
% 3.70/0.98  fof(f60,plain,(
% 3.70/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f61,plain,(
% 3.70/0.98    (k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f60])).
% 3.70/0.98  
% 3.70/0.98  fof(f102,plain,(
% 3.70/0.98    r1_tarski(sK3,sK2)),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f101,plain,(
% 3.70/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f18,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f41,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f18])).
% 3.70/0.98  
% 3.70/0.98  fof(f42,plain,(
% 3.70/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(flattening,[],[f41])).
% 3.70/0.98  
% 3.70/0.98  fof(f58,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(nnf_transformation,[],[f42])).
% 3.70/0.98  
% 3.70/0.98  fof(f90,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f58])).
% 3.70/0.98  
% 3.70/0.98  fof(f99,plain,(
% 3.70/0.98    v1_funct_2(sK4,sK2,sK2)),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f14,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f36,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f14])).
% 3.70/0.98  
% 3.70/0.98  fof(f84,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f36])).
% 3.70/0.98  
% 3.70/0.98  fof(f11,axiom,(
% 3.70/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f32,plain,(
% 3.70/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.70/0.98    inference(ennf_transformation,[],[f11])).
% 3.70/0.98  
% 3.70/0.98  fof(f33,plain,(
% 3.70/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(flattening,[],[f32])).
% 3.70/0.98  
% 3.70/0.98  fof(f81,plain,(
% 3.70/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f33])).
% 3.70/0.98  
% 3.70/0.98  fof(f98,plain,(
% 3.70/0.98    v1_funct_1(sK4)),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f100,plain,(
% 3.70/0.98    v3_funct_2(sK4,sK2,sK2)),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f17,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f39,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f17])).
% 3.70/0.98  
% 3.70/0.98  fof(f40,plain,(
% 3.70/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(flattening,[],[f39])).
% 3.70/0.98  
% 3.70/0.98  fof(f88,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f40])).
% 3.70/0.98  
% 3.70/0.98  fof(f5,axiom,(
% 3.70/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f25,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f5])).
% 3.70/0.98  
% 3.70/0.98  fof(f70,plain,(
% 3.70/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f25])).
% 3.70/0.98  
% 3.70/0.98  fof(f6,axiom,(
% 3.70/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f71,plain,(
% 3.70/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f6])).
% 3.70/0.98  
% 3.70/0.98  fof(f16,axiom,(
% 3.70/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f38,plain,(
% 3.70/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f16])).
% 3.70/0.98  
% 3.70/0.98  fof(f86,plain,(
% 3.70/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f38])).
% 3.70/0.98  
% 3.70/0.98  fof(f103,plain,(
% 3.70/0.98    k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3),
% 3.70/0.98    inference(cnf_transformation,[],[f61])).
% 3.70/0.98  
% 3.70/0.98  fof(f15,axiom,(
% 3.70/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f37,plain,(
% 3.70/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f15])).
% 3.70/0.98  
% 3.70/0.98  fof(f85,plain,(
% 3.70/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f37])).
% 3.70/0.98  
% 3.70/0.98  fof(f89,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f40])).
% 3.70/0.98  
% 3.70/0.98  fof(f19,axiom,(
% 3.70/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f43,plain,(
% 3.70/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.70/0.98    inference(ennf_transformation,[],[f19])).
% 3.70/0.98  
% 3.70/0.98  fof(f44,plain,(
% 3.70/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(flattening,[],[f43])).
% 3.70/0.98  
% 3.70/0.98  fof(f59,plain,(
% 3.70/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(nnf_transformation,[],[f44])).
% 3.70/0.98  
% 3.70/0.98  fof(f96,plain,(
% 3.70/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f59])).
% 3.70/0.98  
% 3.70/0.98  fof(f13,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f22,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.70/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.70/0.98  
% 3.70/0.98  fof(f35,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/0.98    inference(ennf_transformation,[],[f22])).
% 3.70/0.98  
% 3.70/0.98  fof(f83,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f35])).
% 3.70/0.98  
% 3.70/0.98  fof(f10,axiom,(
% 3.70/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f30,plain,(
% 3.70/0.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.70/0.98    inference(ennf_transformation,[],[f10])).
% 3.70/0.98  
% 3.70/0.98  fof(f31,plain,(
% 3.70/0.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(flattening,[],[f30])).
% 3.70/0.98  
% 3.70/0.98  fof(f80,plain,(
% 3.70/0.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f31])).
% 3.70/0.98  
% 3.70/0.98  fof(f4,axiom,(
% 3.70/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f69,plain,(
% 3.70/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f4])).
% 3.70/0.98  
% 3.70/0.98  fof(f2,axiom,(
% 3.70/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f51,plain,(
% 3.70/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.98    inference(nnf_transformation,[],[f2])).
% 3.70/0.98  
% 3.70/0.98  fof(f52,plain,(
% 3.70/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.98    inference(flattening,[],[f51])).
% 3.70/0.98  
% 3.70/0.98  fof(f67,plain,(
% 3.70/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f52])).
% 3.70/0.98  
% 3.70/0.98  cnf(c_37,negated_conjecture,
% 3.70/0.98      ( r1_tarski(sK3,sK2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1238,plain,
% 3.70/0.98      ( r1_tarski(sK3,sK2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_38,negated_conjecture,
% 3.70/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 3.70/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1237,plain,
% 3.70/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_33,plain,
% 3.70/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.70/0.98      | k1_xboole_0 = X2 ),
% 3.70/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1241,plain,
% 3.70/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.70/0.98      | k1_xboole_0 = X1
% 3.70/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1743,plain,
% 3.70/0.98      ( k1_relset_1(sK2,sK2,sK4) = sK2
% 3.70/0.98      | sK2 = k1_xboole_0
% 3.70/0.98      | v1_funct_2(sK4,sK2,sK2) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1237,c_1241]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_40,negated_conjecture,
% 3.70/0.98      ( v1_funct_2(sK4,sK2,sK2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1744,plain,
% 3.70/0.98      ( ~ v1_funct_2(sK4,sK2,sK2)
% 3.70/0.98      | k1_relset_1(sK2,sK2,sK4) = sK2
% 3.70/0.98      | sK2 = k1_xboole_0 ),
% 3.70/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1743]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2025,plain,
% 3.70/0.98      ( sK2 = k1_xboole_0 | k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_1743,c_40,c_1744]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2026,plain,
% 3.70/0.98      ( k1_relset_1(sK2,sK2,sK4) = sK2 | sK2 = k1_xboole_0 ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_2025]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_22,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1251,plain,
% 3.70/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.70/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2693,plain,
% 3.70/0.98      ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1237,c_1251]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2839,plain,
% 3.70/0.98      ( k1_relat_1(sK4) = sK2 | sK2 = k1_xboole_0 ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2026,c_2693]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_19,plain,
% 3.70/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.70/0.98      | ~ v2_funct_1(X1)
% 3.70/0.98      | ~ v1_funct_1(X1)
% 3.70/0.98      | ~ v1_relat_1(X1)
% 3.70/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.70/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1254,plain,
% 3.70/0.98      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.70/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.70/0.98      | v2_funct_1(X0) != iProver_top
% 3.70/0.98      | v1_funct_1(X0) != iProver_top
% 3.70/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5631,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.70/0.98      | sK2 = k1_xboole_0
% 3.70/0.98      | r1_tarski(X0,sK2) != iProver_top
% 3.70/0.98      | v2_funct_1(sK4) != iProver_top
% 3.70/0.98      | v1_funct_1(sK4) != iProver_top
% 3.70/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2839,c_1254]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_41,negated_conjecture,
% 3.70/0.98      ( v1_funct_1(sK4) ),
% 3.70/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_42,plain,
% 3.70/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_39,negated_conjecture,
% 3.70/0.98      ( v3_funct_2(sK4,sK2,sK2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_44,plain,
% 3.70/0.98      ( v3_funct_2(sK4,sK2,sK2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_45,plain,
% 3.70/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_26,plain,
% 3.70/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | v2_funct_1(X0)
% 3.70/0.98      | ~ v1_funct_1(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1713,plain,
% 3.70/0.98      ( ~ v3_funct_2(sK4,X0,X1)
% 3.70/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/0.98      | v2_funct_1(sK4)
% 3.70/0.98      | ~ v1_funct_1(sK4) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1891,plain,
% 3.70/0.98      ( ~ v3_funct_2(sK4,sK2,sK2)
% 3.70/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.70/0.98      | v2_funct_1(sK4)
% 3.70/0.98      | ~ v1_funct_1(sK4) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1713]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1892,plain,
% 3.70/0.98      ( v3_funct_2(sK4,sK2,sK2) != iProver_top
% 3.70/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 3.70/0.98      | v2_funct_1(sK4) = iProver_top
% 3.70/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1891]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/0.98      | ~ v1_relat_1(X1)
% 3.70/0.98      | v1_relat_1(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1761,plain,
% 3.70/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) | v1_relat_1(sK4) ),
% 3.70/0.98      inference(resolution,[status(thm)],[c_8,c_38]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9,plain,
% 3.70/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1903,plain,
% 3.70/0.98      ( v1_relat_1(sK4) ),
% 3.70/0.98      inference(forward_subsumption_resolution,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_1761,c_9]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1904,plain,
% 3.70/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8024,plain,
% 3.70/0.98      ( r1_tarski(X0,sK2) != iProver_top
% 3.70/0.98      | sK2 = k1_xboole_0
% 3.70/0.98      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_5631,c_42,c_44,c_45,c_1892,c_1904]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8025,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.70/0.98      | sK2 = k1_xboole_0
% 3.70/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_8024]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8035,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) = sK3 | sK2 = k1_xboole_0 ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1238,c_8025]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_24,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.70/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1249,plain,
% 3.70/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.70/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3331,plain,
% 3.70/0.98      ( k8_relset_1(sK2,sK2,sK4,X0) = k10_relat_1(sK4,X0) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1237,c_1249]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_36,negated_conjecture,
% 3.70/0.98      ( k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3
% 3.70/0.98      | k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
% 3.70/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3581,plain,
% 3.70/0.98      ( k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) != sK3
% 3.70/0.98      | k10_relat_1(sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_3331,c_36]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3582,plain,
% 3.70/0.98      ( k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) != sK3
% 3.70/0.98      | k10_relat_1(sK4,k7_relset_1(sK2,sK2,sK4,sK3)) != sK3 ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_3581,c_3331]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_23,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.70/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1250,plain,
% 3.70/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.70/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3336,plain,
% 3.70/0.98      ( k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1237,c_1250]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3722,plain,
% 3.70/0.98      ( k9_relat_1(sK4,k10_relat_1(sK4,sK3)) != sK3
% 3.70/0.98      | k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_3582,c_3336]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_25,plain,
% 3.70/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.70/0.98      | v2_funct_2(X0,X2)
% 3.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/0.98      | ~ v1_funct_1(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1248,plain,
% 3.70/0.98      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.70/0.98      | v2_funct_2(X0,X2) = iProver_top
% 3.70/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.70/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5453,plain,
% 3.70/0.98      ( v3_funct_2(sK4,sK2,sK2) != iProver_top
% 3.70/0.98      | v2_funct_2(sK4,sK2) = iProver_top
% 3.70/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1237,c_1248]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1733,plain,
% 3.70/0.98      ( ~ v3_funct_2(sK4,X0,X1)
% 3.70/0.98      | v2_funct_2(sK4,X1)
% 3.70/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.70/0.98      | ~ v1_funct_1(sK4) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1939,plain,
% 3.70/0.98      ( ~ v3_funct_2(sK4,sK2,sK2)
% 3.70/0.98      | v2_funct_2(sK4,sK2)
% 3.70/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.70/0.98      | ~ v1_funct_1(sK4) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1733]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1940,plain,
% 3.70/0.98      ( v3_funct_2(sK4,sK2,sK2) != iProver_top
% 3.70/0.98      | v2_funct_2(sK4,sK2) = iProver_top
% 3.70/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 3.70/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1939]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6324,plain,
% 3.70/0.98      ( v2_funct_2(sK4,sK2) = iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_5453,c_42,c_44,c_45,c_1940]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_35,plain,
% 3.70/0.98      ( ~ v2_funct_2(X0,X1)
% 3.70/0.98      | ~ v5_relat_1(X0,X1)
% 3.70/0.98      | ~ v1_relat_1(X0)
% 3.70/0.98      | k2_relat_1(X0) = X1 ),
% 3.70/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1239,plain,
% 3.70/0.98      ( k2_relat_1(X0) = X1
% 3.70/0.98      | v2_funct_2(X0,X1) != iProver_top
% 3.70/0.98      | v5_relat_1(X0,X1) != iProver_top
% 3.70/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6329,plain,
% 3.70/0.98      ( k2_relat_1(sK4) = sK2
% 3.70/0.98      | v5_relat_1(sK4,sK2) != iProver_top
% 3.70/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6324,c_1239]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_21,plain,
% 3.70/0.98      ( v5_relat_1(X0,X1)
% 3.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.70/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1650,plain,
% 3.70/0.98      ( v5_relat_1(sK4,sK2)
% 3.70/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1837,plain,
% 3.70/0.98      ( ~ v2_funct_2(sK4,sK2)
% 3.70/0.98      | ~ v5_relat_1(sK4,sK2)
% 3.70/0.98      | ~ v1_relat_1(sK4)
% 3.70/0.98      | k2_relat_1(sK4) = sK2 ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_35]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6332,plain,
% 3.70/0.98      ( k2_relat_1(sK4) = sK2 ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_6329,c_41,c_39,c_38,c_1650,c_1837,c_1903,c_1939]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_18,plain,
% 3.70/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.70/0.98      | ~ v1_funct_1(X1)
% 3.70/0.98      | ~ v1_relat_1(X1)
% 3.70/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.70/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1255,plain,
% 3.70/0.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.70/0.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.70/0.98      | v1_funct_1(X0) != iProver_top
% 3.70/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6358,plain,
% 3.70/0.98      ( k9_relat_1(sK4,k10_relat_1(sK4,X0)) = X0
% 3.70/0.98      | r1_tarski(X0,sK2) != iProver_top
% 3.70/0.98      | v1_funct_1(sK4) != iProver_top
% 3.70/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6332,c_1255]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7047,plain,
% 3.70/0.98      ( k9_relat_1(sK4,k10_relat_1(sK4,X0)) = X0
% 3.70/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_6358,c_42,c_1904]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7055,plain,
% 3.70/0.98      ( k9_relat_1(sK4,k10_relat_1(sK4,sK3)) = sK3 ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1238,c_7047]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8314,plain,
% 3.70/0.98      ( sK2 = k1_xboole_0 ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_8035,c_3722,c_7055]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8339,plain,
% 3.70/0.98      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_8314,c_1238]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7,plain,
% 3.70/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1266,plain,
% 3.70/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3,plain,
% 3.70/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.70/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1269,plain,
% 3.70/0.98      ( X0 = X1
% 3.70/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.70/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2699,plain,
% 3.70/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_1266,c_1269]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8414,plain,
% 3.70/0.98      ( sK3 = k1_xboole_0 ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_8339,c_2699]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7061,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 | sK3 != sK3 ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_7055,c_3722]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7890,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
% 3.70/0.98      inference(equality_resolution_simp,[status(thm)],[c_7061]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9685,plain,
% 3.70/0.98      ( k10_relat_1(sK4,k9_relat_1(sK4,k1_xboole_0)) != k1_xboole_0 ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_8414,c_7890]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2442,plain,
% 3.70/0.98      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2065,plain,
% 3.70/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.70/0.98      | ~ v2_funct_1(sK4)
% 3.70/0.98      | ~ v1_funct_1(sK4)
% 3.70/0.98      | ~ v1_relat_1(sK4)
% 3.70/0.98      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2067,plain,
% 3.70/0.98      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
% 3.70/0.98      | ~ v2_funct_1(sK4)
% 3.70/0.98      | ~ v1_funct_1(sK4)
% 3.70/0.98      | ~ v1_relat_1(sK4)
% 3.70/0.98      | k10_relat_1(sK4,k9_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2065]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(contradiction,plain,
% 3.70/0.98      ( $false ),
% 3.70/0.98      inference(minisat,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_9685,c_2442,c_2067,c_1903,c_1891,c_38,c_39,c_41]) ).
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  ------                               Statistics
% 3.70/0.98  
% 3.70/0.98  ------ Selected
% 3.70/0.98  
% 3.70/0.98  total_time:                             0.337
% 3.70/0.98  
%------------------------------------------------------------------------------
