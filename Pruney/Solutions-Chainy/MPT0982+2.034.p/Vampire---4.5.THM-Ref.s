%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:31 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 474 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  430 (3493 expanded)
%              Number of equality atoms :  133 (1105 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1384,f288])).

fof(f288,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f67,f106])).

fof(f106,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f60,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f67,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f1384,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1379,f788])).

fof(f788,plain,(
    sK1 = k10_relat_1(sK4,sK2) ),
    inference(resolution,[],[f774,f318])).

fof(f318,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f314,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f314,plain,(
    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f313,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f313,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f84,f131])).

fof(f131,plain,(
    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f63,f83])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f774,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | sK1 = k10_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f773,f733])).

fof(f733,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK4,X0),sK1) ),
    inference(resolution,[],[f732,f80])).

fof(f732,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f731,f63])).

fof(f731,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    inference(superposition,[],[f93,f134])).

fof(f134,plain,(
    ! [X0] : k8_relset_1(sK1,sK2,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f773,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | sK1 = k10_relat_1(sK4,X0)
      | ~ r1_tarski(k10_relat_1(sK4,X0),sK1) ) ),
    inference(resolution,[],[f761,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f761,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k10_relat_1(sK4,X0))
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(subsumption_resolution,[],[f760,f99])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f760,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,sK1)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | r1_tarski(sK1,k10_relat_1(sK4,X0)) ) ),
    inference(forward_demodulation,[],[f759,f291])).

fof(f291,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f130,f140])).

fof(f140,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f139,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f133,f62])).

fof(f62,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f133,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f63,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f130,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f63,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f759,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | r1_tarski(sK1,k10_relat_1(sK4,X0))
      | ~ r1_tarski(sK1,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f758,f142])).

fof(f142,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f138,f73])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f138,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f63,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f758,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | r1_tarski(sK1,k10_relat_1(sK4,X0))
      | ~ r1_tarski(sK1,k1_relat_1(sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f757,f61])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f757,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | r1_tarski(sK1,k10_relat_1(sK4,X0))
      | ~ r1_tarski(sK1,k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f92,f754])).

fof(f754,plain,(
    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) ),
    inference(superposition,[],[f143,f211])).

fof(f211,plain,(
    sK4 = k7_relat_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f210,f142])).

fof(f210,plain,
    ( sK4 = k7_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f132,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f132,plain,(
    v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f63,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f143,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f142,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f1379,plain,(
    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f922,f1374])).

fof(f1374,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f1086,f1129])).

fof(f1129,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f64,f911])).

fof(f911,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f906,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f906,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f141,f60])).

fof(f141,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X1,sK4) = k1_partfun1(X2,X3,sK1,sK2,X1,sK4)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f135,f61])).

fof(f135,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X1,sK4) = k1_partfun1(X2,X3,sK1,sK2,X1,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f63,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1086,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f1013,f83])).

fof(f1013,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1012,f60])).

fof(f1012,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1011,f63])).

fof(f1011,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f97,f813])).

fof(f813,plain,(
    k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f136,f60])).

fof(f136,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k4_relset_1(X4,X5,sK1,sK2,X6,sK4) = k5_relat_1(X6,sK4) ) ),
    inference(resolution,[],[f63,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f922,plain,(
    k2_relat_1(sK3) = k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) ),
    inference(backward_demodulation,[],[f825,f919])).

fof(f919,plain,(
    k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f144,f125])).

fof(f125,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f113,f73])).

fof(f113,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f60,f69])).

fof(f144,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,sK4)) = k9_relat_1(sK4,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f142,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f825,plain,(
    k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) ),
    inference(resolution,[],[f297,f302])).

fof(f302,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(resolution,[],[f290,f80])).

fof(f290,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f289,f60])).

fof(f289,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f84,f106])).

fof(f297,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f296,f142])).

fof(f296,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f295,f61])).

fof(f295,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f292,f65])).

fof(f65,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f292,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v2_funct_1(sK4)
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f75,f291])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (2606)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (2607)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (2599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (2617)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (2600)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (2609)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (2604)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (2614)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (2595)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (2601)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (2598)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (2620)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (2605)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (2615)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (2608)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (2597)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (2610)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (2616)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (2601)Refutation not found, incomplete strategy% (2601)------------------------------
% 0.20/0.52  % (2601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2601)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2601)Memory used [KB]: 10874
% 0.20/0.52  % (2601)Time elapsed: 0.078 s
% 0.20/0.52  % (2601)------------------------------
% 0.20/0.52  % (2601)------------------------------
% 0.20/0.52  % (2612)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (2613)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (2596)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2602)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (2618)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (2619)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (2611)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (2603)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.71/0.59  % (2596)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.61  % SZS output start Proof for theBenchmark
% 1.71/0.61  fof(f1385,plain,(
% 1.71/0.61    $false),
% 1.71/0.61    inference(subsumption_resolution,[],[f1384,f288])).
% 1.71/0.61  fof(f288,plain,(
% 1.71/0.61    sK1 != k2_relat_1(sK3)),
% 1.71/0.61    inference(superposition,[],[f67,f106])).
% 1.71/0.61  fof(f106,plain,(
% 1.71/0.61    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.71/0.61    inference(resolution,[],[f60,f83])).
% 1.71/0.61  fof(f83,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f36])).
% 1.71/0.61  fof(f36,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f15])).
% 1.71/0.61  fof(f15,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.71/0.61  fof(f60,plain,(
% 1.71/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f53,plain,(
% 1.71/0.61    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f52,f51])).
% 1.71/0.61  fof(f51,plain,(
% 1.71/0.61    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f52,plain,(
% 1.71/0.61    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f25,plain,(
% 1.71/0.61    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.71/0.61    inference(flattening,[],[f24])).
% 1.71/0.61  fof(f24,plain,(
% 1.71/0.61    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.71/0.61    inference(ennf_transformation,[],[f22])).
% 1.71/0.61  fof(f22,negated_conjecture,(
% 1.71/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.71/0.61    inference(negated_conjecture,[],[f21])).
% 1.71/0.61  fof(f21,conjecture,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.71/0.61  fof(f67,plain,(
% 1.71/0.61    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f1384,plain,(
% 1.71/0.61    sK1 = k2_relat_1(sK3)),
% 1.71/0.61    inference(forward_demodulation,[],[f1379,f788])).
% 1.71/0.61  fof(f788,plain,(
% 1.71/0.61    sK1 = k10_relat_1(sK4,sK2)),
% 1.71/0.61    inference(resolution,[],[f774,f318])).
% 1.71/0.61  fof(f318,plain,(
% 1.71/0.61    r1_tarski(k2_relat_1(sK4),sK2)),
% 1.71/0.61    inference(resolution,[],[f314,f80])).
% 1.71/0.61  fof(f80,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f56])).
% 1.71/0.61  fof(f56,plain,(
% 1.71/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.61    inference(nnf_transformation,[],[f2])).
% 1.71/0.61  fof(f2,axiom,(
% 1.71/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.61  fof(f314,plain,(
% 1.71/0.61    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2))),
% 1.71/0.61    inference(subsumption_resolution,[],[f313,f63])).
% 1.71/0.61  fof(f63,plain,(
% 1.71/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f313,plain,(
% 1.71/0.61    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.61    inference(superposition,[],[f84,f131])).
% 1.71/0.61  fof(f131,plain,(
% 1.71/0.61    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)),
% 1.71/0.61    inference(resolution,[],[f63,f83])).
% 1.71/0.61  fof(f84,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f37])).
% 1.71/0.61  fof(f37,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f11])).
% 1.71/0.61  fof(f11,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.71/0.61  fof(f774,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | sK1 = k10_relat_1(sK4,X0)) )),
% 1.71/0.61    inference(subsumption_resolution,[],[f773,f733])).
% 1.71/0.61  fof(f733,plain,(
% 1.71/0.61    ( ! [X0] : (r1_tarski(k10_relat_1(sK4,X0),sK1)) )),
% 1.71/0.61    inference(resolution,[],[f732,f80])).
% 1.71/0.61  fof(f732,plain,(
% 1.71/0.61    ( ! [X0] : (m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(sK1))) )),
% 1.71/0.61    inference(subsumption_resolution,[],[f731,f63])).
% 1.71/0.61  fof(f731,plain,(
% 1.71/0.61    ( ! [X0] : (m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) )),
% 1.71/0.61    inference(superposition,[],[f93,f134])).
% 1.71/0.61  fof(f134,plain,(
% 1.71/0.61    ( ! [X0] : (k8_relset_1(sK1,sK2,sK4,X0) = k10_relat_1(sK4,X0)) )),
% 1.71/0.61    inference(resolution,[],[f63,f94])).
% 1.71/0.61  fof(f94,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f44])).
% 1.71/0.61  fof(f44,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f17])).
% 1.71/0.61  fof(f17,axiom,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.71/0.61  fof(f93,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f43])).
% 1.71/0.61  fof(f43,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f13])).
% 1.71/0.61  fof(f13,axiom,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.71/0.61  fof(f773,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | sK1 = k10_relat_1(sK4,X0) | ~r1_tarski(k10_relat_1(sK4,X0),sK1)) )),
% 1.71/0.61    inference(resolution,[],[f761,f79])).
% 1.71/0.61  fof(f79,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f55])).
% 1.71/0.61  fof(f55,plain,(
% 1.71/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.61    inference(flattening,[],[f54])).
% 1.71/0.61  fof(f54,plain,(
% 1.71/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.61    inference(nnf_transformation,[],[f1])).
% 1.71/0.61  fof(f1,axiom,(
% 1.71/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.61  fof(f761,plain,(
% 1.71/0.61    ( ! [X0] : (r1_tarski(sK1,k10_relat_1(sK4,X0)) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 1.71/0.61    inference(subsumption_resolution,[],[f760,f99])).
% 1.71/0.61  fof(f99,plain,(
% 1.71/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.61    inference(equality_resolution,[],[f77])).
% 1.71/0.61  fof(f77,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.71/0.61    inference(cnf_transformation,[],[f55])).
% 1.71/0.61  fof(f760,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(sK1,sK1) | ~r1_tarski(k2_relat_1(sK4),X0) | r1_tarski(sK1,k10_relat_1(sK4,X0))) )),
% 1.71/0.61    inference(forward_demodulation,[],[f759,f291])).
% 1.71/0.61  fof(f291,plain,(
% 1.71/0.61    sK1 = k1_relat_1(sK4)),
% 1.71/0.61    inference(forward_demodulation,[],[f130,f140])).
% 1.71/0.61  fof(f140,plain,(
% 1.71/0.61    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.71/0.61    inference(subsumption_resolution,[],[f139,f66])).
% 1.71/0.61  fof(f66,plain,(
% 1.71/0.61    k1_xboole_0 != sK2),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f139,plain,(
% 1.71/0.61    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.71/0.61    inference(subsumption_resolution,[],[f133,f62])).
% 1.71/0.61  fof(f62,plain,(
% 1.71/0.61    v1_funct_2(sK4,sK1,sK2)),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f133,plain,(
% 1.71/0.61    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.71/0.61    inference(resolution,[],[f63,f86])).
% 1.71/0.61  fof(f86,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f57])).
% 1.71/0.61  fof(f57,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(nnf_transformation,[],[f40])).
% 1.71/0.61  fof(f40,plain,(
% 1.71/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(flattening,[],[f39])).
% 1.71/0.61  fof(f39,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f18])).
% 1.71/0.61  fof(f18,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.61  fof(f130,plain,(
% 1.71/0.61    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.71/0.61    inference(resolution,[],[f63,f82])).
% 1.71/0.61  fof(f82,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f35])).
% 1.71/0.61  fof(f35,plain,(
% 1.71/0.61    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.61    inference(ennf_transformation,[],[f14])).
% 1.71/0.61  fof(f14,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.61  fof(f759,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | r1_tarski(sK1,k10_relat_1(sK4,X0)) | ~r1_tarski(sK1,k1_relat_1(sK4))) )),
% 1.71/0.61    inference(subsumption_resolution,[],[f758,f142])).
% 1.71/0.61  fof(f142,plain,(
% 1.71/0.61    v1_relat_1(sK4)),
% 1.71/0.61    inference(subsumption_resolution,[],[f138,f73])).
% 1.71/0.61  fof(f73,plain,(
% 1.71/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f4])).
% 1.71/0.61  fof(f4,axiom,(
% 1.71/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.61  fof(f138,plain,(
% 1.71/0.61    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.71/0.61    inference(resolution,[],[f63,f69])).
% 1.71/0.61  fof(f69,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f27])).
% 1.71/0.61  fof(f27,plain,(
% 1.71/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.61    inference(ennf_transformation,[],[f3])).
% 1.71/0.61  fof(f3,axiom,(
% 1.71/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.61  fof(f758,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | r1_tarski(sK1,k10_relat_1(sK4,X0)) | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4)) )),
% 1.71/0.61    inference(subsumption_resolution,[],[f757,f61])).
% 1.71/0.61  fof(f61,plain,(
% 1.71/0.61    v1_funct_1(sK4)),
% 1.71/0.61    inference(cnf_transformation,[],[f53])).
% 1.71/0.61  fof(f757,plain,(
% 1.71/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | r1_tarski(sK1,k10_relat_1(sK4,X0)) | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.71/0.61    inference(superposition,[],[f92,f754])).
% 1.71/0.61  fof(f754,plain,(
% 1.71/0.61    k2_relat_1(sK4) = k9_relat_1(sK4,sK1)),
% 1.71/0.61    inference(superposition,[],[f143,f211])).
% 1.71/0.61  fof(f211,plain,(
% 1.71/0.61    sK4 = k7_relat_1(sK4,sK1)),
% 1.71/0.61    inference(subsumption_resolution,[],[f210,f142])).
% 1.71/0.61  fof(f210,plain,(
% 1.71/0.61    sK4 = k7_relat_1(sK4,sK1) | ~v1_relat_1(sK4)),
% 1.71/0.61    inference(resolution,[],[f132,f76])).
% 1.71/0.61  fof(f76,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f34])).
% 1.71/0.61  fof(f34,plain,(
% 1.71/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.61    inference(flattening,[],[f33])).
% 1.71/0.61  fof(f33,plain,(
% 1.71/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.71/0.61    inference(ennf_transformation,[],[f7])).
% 1.71/0.62  fof(f7,axiom,(
% 1.71/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.71/0.62  fof(f132,plain,(
% 1.71/0.62    v4_relat_1(sK4,sK1)),
% 1.71/0.62    inference(resolution,[],[f63,f85])).
% 1.71/0.62  fof(f85,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f38])).
% 1.71/0.62  fof(f38,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(ennf_transformation,[],[f23])).
% 1.71/0.62  fof(f23,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.71/0.62    inference(pure_predicate_removal,[],[f10])).
% 1.71/0.62  fof(f10,axiom,(
% 1.71/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.62  fof(f143,plain,(
% 1.71/0.62    ( ! [X0] : (k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)) )),
% 1.71/0.62    inference(resolution,[],[f142,f74])).
% 1.71/0.62  fof(f74,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f30])).
% 1.71/0.62  fof(f30,plain,(
% 1.71/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(ennf_transformation,[],[f5])).
% 1.71/0.62  fof(f5,axiom,(
% 1.71/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.71/0.62  fof(f92,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f42])).
% 1.71/0.62  fof(f42,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.71/0.62    inference(flattening,[],[f41])).
% 1.71/0.62  fof(f41,plain,(
% 1.71/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.71/0.62    inference(ennf_transformation,[],[f8])).
% 1.71/0.62  fof(f8,axiom,(
% 1.71/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.71/0.62  fof(f1379,plain,(
% 1.71/0.62    k2_relat_1(sK3) = k10_relat_1(sK4,sK2)),
% 1.71/0.62    inference(backward_demodulation,[],[f922,f1374])).
% 1.71/0.62  fof(f1374,plain,(
% 1.71/0.62    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.71/0.62    inference(forward_demodulation,[],[f1086,f1129])).
% 1.71/0.62  fof(f1129,plain,(
% 1.71/0.62    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.71/0.62    inference(backward_demodulation,[],[f64,f911])).
% 1.71/0.62  fof(f911,plain,(
% 1.71/0.62    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.71/0.62    inference(subsumption_resolution,[],[f906,f58])).
% 1.71/0.62  fof(f58,plain,(
% 1.71/0.62    v1_funct_1(sK3)),
% 1.71/0.62    inference(cnf_transformation,[],[f53])).
% 1.71/0.62  fof(f906,plain,(
% 1.71/0.62    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.71/0.62    inference(resolution,[],[f141,f60])).
% 1.71/0.62  fof(f141,plain,(
% 1.71/0.62    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(X1,sK4) = k1_partfun1(X2,X3,sK1,sK2,X1,sK4) | ~v1_funct_1(X1)) )),
% 1.71/0.62    inference(subsumption_resolution,[],[f135,f61])).
% 1.71/0.62  fof(f135,plain,(
% 1.71/0.62    ( ! [X2,X3,X1] : (k5_relat_1(X1,sK4) = k1_partfun1(X2,X3,sK1,sK2,X1,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1)) )),
% 1.71/0.62    inference(resolution,[],[f63,f95])).
% 1.71/0.62  fof(f95,plain,(
% 1.71/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f46])).
% 1.71/0.62  fof(f46,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.62    inference(flattening,[],[f45])).
% 1.71/0.62  fof(f45,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.62    inference(ennf_transformation,[],[f19])).
% 1.71/0.62  fof(f19,axiom,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.71/0.62  fof(f64,plain,(
% 1.71/0.62    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.71/0.62    inference(cnf_transformation,[],[f53])).
% 1.71/0.62  fof(f1086,plain,(
% 1.71/0.62    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.71/0.62    inference(resolution,[],[f1013,f83])).
% 1.71/0.62  fof(f1013,plain,(
% 1.71/0.62    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.71/0.62    inference(subsumption_resolution,[],[f1012,f60])).
% 1.71/0.62  fof(f1012,plain,(
% 1.71/0.62    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.62    inference(subsumption_resolution,[],[f1011,f63])).
% 1.71/0.62  fof(f1011,plain,(
% 1.71/0.62    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.62    inference(superposition,[],[f97,f813])).
% 1.71/0.62  fof(f813,plain,(
% 1.71/0.62    k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.71/0.62    inference(resolution,[],[f136,f60])).
% 1.71/0.62  fof(f136,plain,(
% 1.71/0.62    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(X4,X5,sK1,sK2,X6,sK4) = k5_relat_1(X6,sK4)) )),
% 1.71/0.62    inference(resolution,[],[f63,f96])).
% 1.71/0.62  fof(f96,plain,(
% 1.71/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f48])).
% 1.71/0.62  fof(f48,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(flattening,[],[f47])).
% 1.71/0.62  fof(f47,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.62    inference(ennf_transformation,[],[f16])).
% 1.71/0.62  fof(f16,axiom,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.71/0.62  fof(f97,plain,(
% 1.71/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f50])).
% 1.71/0.62  fof(f50,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(flattening,[],[f49])).
% 1.71/0.62  fof(f49,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.62    inference(ennf_transformation,[],[f12])).
% 1.71/0.62  fof(f12,axiom,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.71/0.62  fof(f922,plain,(
% 1.71/0.62    k2_relat_1(sK3) = k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4)))),
% 1.71/0.62    inference(backward_demodulation,[],[f825,f919])).
% 1.71/0.62  fof(f919,plain,(
% 1.71/0.62    k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.71/0.62    inference(resolution,[],[f144,f125])).
% 1.71/0.62  fof(f125,plain,(
% 1.71/0.62    v1_relat_1(sK3)),
% 1.71/0.62    inference(subsumption_resolution,[],[f113,f73])).
% 1.71/0.62  fof(f113,plain,(
% 1.71/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.71/0.62    inference(resolution,[],[f60,f69])).
% 1.71/0.62  fof(f144,plain,(
% 1.71/0.62    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,sK4)) = k9_relat_1(sK4,k2_relat_1(X1))) )),
% 1.71/0.62    inference(resolution,[],[f142,f68])).
% 1.71/0.62  fof(f68,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f26])).
% 1.71/0.62  fof(f26,plain,(
% 1.71/0.62    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.62    inference(ennf_transformation,[],[f6])).
% 1.71/0.62  fof(f6,axiom,(
% 1.71/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.71/0.62  fof(f825,plain,(
% 1.71/0.62    k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3)))),
% 1.71/0.62    inference(resolution,[],[f297,f302])).
% 1.71/0.62  fof(f302,plain,(
% 1.71/0.62    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.71/0.62    inference(resolution,[],[f290,f80])).
% 1.71/0.62  fof(f290,plain,(
% 1.71/0.62    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 1.71/0.62    inference(subsumption_resolution,[],[f289,f60])).
% 1.71/0.62  fof(f289,plain,(
% 1.71/0.62    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.62    inference(superposition,[],[f84,f106])).
% 1.71/0.62  fof(f297,plain,(
% 1.71/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) )),
% 1.71/0.62    inference(subsumption_resolution,[],[f296,f142])).
% 1.71/0.62  fof(f296,plain,(
% 1.71/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 | ~v1_relat_1(sK4)) )),
% 1.71/0.62    inference(subsumption_resolution,[],[f295,f61])).
% 1.71/0.62  fof(f295,plain,(
% 1.71/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.71/0.62    inference(subsumption_resolution,[],[f292,f65])).
% 1.71/0.62  fof(f65,plain,(
% 1.71/0.62    v2_funct_1(sK4)),
% 1.71/0.62    inference(cnf_transformation,[],[f53])).
% 1.71/0.62  fof(f292,plain,(
% 1.71/0.62    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v2_funct_1(sK4) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.71/0.62    inference(superposition,[],[f75,f291])).
% 1.71/0.62  fof(f75,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f32])).
% 1.71/0.62  fof(f32,plain,(
% 1.71/0.62    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(flattening,[],[f31])).
% 1.71/0.62  fof(f31,plain,(
% 1.71/0.62    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.71/0.62    inference(ennf_transformation,[],[f9])).
% 1.71/0.62  fof(f9,axiom,(
% 1.71/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.71/0.62  % SZS output end Proof for theBenchmark
% 1.71/0.62  % (2596)------------------------------
% 1.71/0.62  % (2596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.62  % (2596)Termination reason: Refutation
% 1.71/0.62  
% 1.71/0.62  % (2596)Memory used [KB]: 11385
% 1.71/0.62  % (2596)Time elapsed: 0.193 s
% 1.71/0.62  % (2596)------------------------------
% 1.71/0.62  % (2596)------------------------------
% 1.71/0.62  % (2594)Success in time 0.262 s
%------------------------------------------------------------------------------
