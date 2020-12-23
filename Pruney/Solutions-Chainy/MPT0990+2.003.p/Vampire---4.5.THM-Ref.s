%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  186 (2358 expanded)
%              Number of leaves         :   26 ( 443 expanded)
%              Depth                    :   31
%              Number of atoms          :  555 (16180 expanded)
%              Number of equality atoms :  158 (5031 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2313,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2180,f70])).

fof(f70,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f2180,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f1583,f2161])).

fof(f2161,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f2160,f440])).

fof(f440,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(resolution,[],[f311,f119])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f311,plain,(
    ! [X14] :
      ( ~ r1_tarski(sK1,X14)
      | sK2 = k5_relat_1(sK2,k6_partfun1(X14)) ) ),
    inference(forward_demodulation,[],[f310,f276])).

fof(f276,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f262,f65])).

fof(f65,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f262,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f73,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f310,plain,(
    ! [X14] :
      ( ~ r1_tarski(k2_relat_1(sK2),X14)
      | sK2 = k5_relat_1(sK2,k6_partfun1(X14)) ) ),
    inference(resolution,[],[f261,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1 ) ),
    inference(definition_unfolding,[],[f93,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f261,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2160,plain,(
    k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f2159,f1576])).

fof(f1576,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f250,f1573])).

fof(f1573,plain,(
    sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f1572,f1449])).

fof(f1449,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1448,f1261])).

fof(f1261,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f785,f1234])).

fof(f1234,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1233,f790])).

fof(f790,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f786,f784])).

fof(f784,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f780,f71])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f780,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f200,f73])).

fof(f200,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X6)
      | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f192,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3) ) ),
    inference(resolution,[],[f64,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f786,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f360,f784])).

fof(f360,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f358,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f358,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f66,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f1233,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1232,f64])).

fof(f1232,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1231,f62])).

fof(f1231,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1230,f73])).

fof(f1230,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1229,f71])).

fof(f1229,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f110,f784])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f785,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f66,f784])).

fof(f1448,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1447,f1260])).

fof(f1260,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f784,f1234])).

fof(f1447,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1446,f73])).

fof(f1446,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1445,f71])).

fof(f1445,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f198,f72])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f198,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK0,sK1)
      | ~ v1_funct_1(X1)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f177,f184])).

fof(f184,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f64,f102])).

fof(f177,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f176,f64])).

fof(f176,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f173,f62])).

fof(f173,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f63,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1572,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1571,f62])).

fof(f1571,plain,
    ( ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1557,f183])).

fof(f183,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f101])).

fof(f1557,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f1554,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1554,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1553,f276])).

fof(f1553,plain,
    ( sK1 != k2_relat_1(sK2)
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1552,f1269])).

fof(f1269,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1268,f429])).

fof(f429,plain,(
    sK1 = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f423,f276])).

fof(f423,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f302,f314])).

fof(f314,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f312,f261])).

fof(f312,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f263,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f263,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f73,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f302,plain,(
    ! [X10] : k2_relat_1(k7_relat_1(sK2,X10)) = k9_relat_1(sK2,X10) ),
    inference(resolution,[],[f261,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1268,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f1259,f113])).

fof(f113,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1259,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) ),
    inference(backward_demodulation,[],[f537,f1234])).

fof(f537,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(backward_demodulation,[],[f430,f535])).

fof(f535,plain,(
    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f205,f261])).

fof(f205,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,sK3)) = k10_relat_1(X1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f183,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f430,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[],[f280,f230])).

fof(f230,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f228,f183])).

fof(f228,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f185,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f185,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f64,f103])).

fof(f280,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4 ) ),
    inference(subsumption_resolution,[],[f277,f261])).

fof(f277,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK1)
      | ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4 ) ),
    inference(backward_demodulation,[],[f161,f276])).

fof(f161,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(X4,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4 ) ),
    inference(resolution,[],[f71,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1552,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1551,f71])).

fof(f1551,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1550,f261])).

fof(f1550,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1549,f62])).

fof(f1549,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1548,f183])).

fof(f1548,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1546,f111])).

fof(f111,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1546,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(superposition,[],[f91,f1234])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f250,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(resolution,[],[f203,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f80,f75])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f203,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f183,f122])).

fof(f122,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f62,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f2159,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f2155,f1562])).

fof(f1562,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f1561,f1269])).

fof(f1561,plain,(
    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1560,f62])).

fof(f1560,plain,
    ( ~ v1_funct_1(sK3)
    | k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1555,f183])).

fof(f1555,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f1554,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f88,f75])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f2155,plain,(
    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f2092,f203])).

fof(f2092,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k5_relat_1(sK2,k5_relat_1(sK3,X16)) = k5_relat_1(k6_partfun1(sK0),X16) ) ),
    inference(forward_demodulation,[],[f2089,f1234])).

fof(f2089,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(sK2,sK3),X16) = k5_relat_1(sK2,k5_relat_1(sK3,X16)) ) ),
    inference(resolution,[],[f207,f261])).

fof(f207,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,sK3),X5) = k5_relat_1(X4,k5_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f183,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1583,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1582,f62])).

fof(f1582,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1559,f183])).

fof(f1559,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f1554,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (32309)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (32302)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (32301)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (32310)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (32300)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (32299)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (32294)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (32293)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (32307)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (32308)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (32315)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (32292)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (32316)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (32317)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (32296)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32314)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (32304)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (32305)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (32297)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (32298)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (32291)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (32319)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (32318)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (32306)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (32311)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (32306)Refutation not found, incomplete strategy% (32306)------------------------------
% 0.21/0.55  % (32306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32306)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32306)Memory used [KB]: 10746
% 0.21/0.55  % (32306)Time elapsed: 0.140 s
% 0.21/0.55  % (32306)------------------------------
% 0.21/0.55  % (32306)------------------------------
% 0.21/0.55  % (32290)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (32313)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.56  % (32303)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.57  % (32295)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.57  % (32312)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.62  % (32307)Refutation found. Thanks to Tanya!
% 1.57/0.62  % SZS status Theorem for theBenchmark
% 1.98/0.64  % SZS output start Proof for theBenchmark
% 1.98/0.64  fof(f2313,plain,(
% 1.98/0.64    $false),
% 1.98/0.64    inference(subsumption_resolution,[],[f2180,f70])).
% 1.98/0.64  fof(f70,plain,(
% 1.98/0.64    sK3 != k2_funct_1(sK2)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f29,plain,(
% 1.98/0.64    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.98/0.64    inference(flattening,[],[f28])).
% 1.98/0.64  fof(f28,plain,(
% 1.98/0.64    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.98/0.64    inference(ennf_transformation,[],[f27])).
% 1.98/0.64  fof(f27,negated_conjecture,(
% 1.98/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.98/0.64    inference(negated_conjecture,[],[f26])).
% 1.98/0.64  fof(f26,conjecture,(
% 1.98/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.98/0.64  fof(f2180,plain,(
% 1.98/0.64    sK3 = k2_funct_1(sK2)),
% 1.98/0.64    inference(backward_demodulation,[],[f1583,f2161])).
% 1.98/0.64  fof(f2161,plain,(
% 1.98/0.64    sK2 = k2_funct_1(sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f2160,f440])).
% 1.98/0.64  fof(f440,plain,(
% 1.98/0.64    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.98/0.64    inference(resolution,[],[f311,f119])).
% 1.98/0.64  fof(f119,plain,(
% 1.98/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.98/0.64    inference(equality_resolution,[],[f98])).
% 1.98/0.64  fof(f98,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.98/0.64    inference(cnf_transformation,[],[f1])).
% 1.98/0.64  fof(f1,axiom,(
% 1.98/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.98/0.64  fof(f311,plain,(
% 1.98/0.64    ( ! [X14] : (~r1_tarski(sK1,X14) | sK2 = k5_relat_1(sK2,k6_partfun1(X14))) )),
% 1.98/0.64    inference(forward_demodulation,[],[f310,f276])).
% 1.98/0.64  fof(f276,plain,(
% 1.98/0.64    sK1 = k2_relat_1(sK2)),
% 1.98/0.64    inference(forward_demodulation,[],[f262,f65])).
% 1.98/0.64  fof(f65,plain,(
% 1.98/0.64    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f262,plain,(
% 1.98/0.64    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.98/0.64    inference(resolution,[],[f73,f102])).
% 1.98/0.64  fof(f102,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f52])).
% 1.98/0.64  fof(f52,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.64    inference(ennf_transformation,[],[f19])).
% 1.98/0.64  fof(f19,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.98/0.64  fof(f73,plain,(
% 1.98/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f310,plain,(
% 1.98/0.64    ( ! [X14] : (~r1_tarski(k2_relat_1(sK2),X14) | sK2 = k5_relat_1(sK2,k6_partfun1(X14))) )),
% 1.98/0.64    inference(resolution,[],[f261,f117])).
% 1.98/0.64  fof(f117,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1) )),
% 1.98/0.64    inference(definition_unfolding,[],[f93,f75])).
% 1.98/0.64  fof(f75,plain,(
% 1.98/0.64    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f24])).
% 1.98/0.64  fof(f24,axiom,(
% 1.98/0.64    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.98/0.64  fof(f93,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.98/0.64    inference(cnf_transformation,[],[f45])).
% 1.98/0.64  fof(f45,plain,(
% 1.98/0.64    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(flattening,[],[f44])).
% 1.98/0.64  fof(f44,plain,(
% 1.98/0.64    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(ennf_transformation,[],[f9])).
% 1.98/0.64  fof(f9,axiom,(
% 1.98/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.98/0.64  fof(f261,plain,(
% 1.98/0.64    v1_relat_1(sK2)),
% 1.98/0.64    inference(resolution,[],[f73,f101])).
% 1.98/0.64  fof(f101,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f51])).
% 1.98/0.64  fof(f51,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.64    inference(ennf_transformation,[],[f17])).
% 1.98/0.64  fof(f17,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.98/0.64  fof(f2160,plain,(
% 1.98/0.64    k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.98/0.64    inference(forward_demodulation,[],[f2159,f1576])).
% 1.98/0.64  fof(f1576,plain,(
% 1.98/0.64    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.98/0.64    inference(backward_demodulation,[],[f250,f1573])).
% 1.98/0.64  fof(f1573,plain,(
% 1.98/0.64    sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.98/0.64    inference(forward_demodulation,[],[f1572,f1449])).
% 1.98/0.64  fof(f1449,plain,(
% 1.98/0.64    sK0 = k2_relat_1(sK3)),
% 1.98/0.64    inference(subsumption_resolution,[],[f1448,f1261])).
% 1.98/0.64  fof(f1261,plain,(
% 1.98/0.64    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.98/0.64    inference(backward_demodulation,[],[f785,f1234])).
% 1.98/0.64  fof(f1234,plain,(
% 1.98/0.64    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.98/0.64    inference(resolution,[],[f1233,f790])).
% 1.98/0.64  fof(f790,plain,(
% 1.98/0.64    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f786,f784])).
% 1.98/0.64  fof(f784,plain,(
% 1.98/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.98/0.64    inference(subsumption_resolution,[],[f780,f71])).
% 1.98/0.64  fof(f71,plain,(
% 1.98/0.64    v1_funct_1(sK2)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f780,plain,(
% 1.98/0.64    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.98/0.64    inference(resolution,[],[f200,f73])).
% 1.98/0.64  fof(f200,plain,(
% 1.98/0.64    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X6) | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3)) )),
% 1.98/0.64    inference(subsumption_resolution,[],[f192,f62])).
% 1.98/0.64  fof(f62,plain,(
% 1.98/0.64    v1_funct_1(sK3)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f192,plain,(
% 1.98/0.64    ( ! [X6,X8,X7] : (~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(sK3) | k1_partfun1(X7,X8,sK1,sK0,X6,sK3) = k5_relat_1(X6,sK3)) )),
% 1.98/0.64    inference(resolution,[],[f64,f108])).
% 1.98/0.64  fof(f108,plain,(
% 1.98/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f59])).
% 1.98/0.64  fof(f59,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.98/0.64    inference(flattening,[],[f58])).
% 1.98/0.64  fof(f58,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.98/0.64    inference(ennf_transformation,[],[f23])).
% 1.98/0.64  fof(f23,axiom,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.98/0.64  fof(f64,plain,(
% 1.98/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f786,plain,(
% 1.98/0.64    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.98/0.64    inference(backward_demodulation,[],[f360,f784])).
% 1.98/0.64  fof(f360,plain,(
% 1.98/0.64    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.98/0.64    inference(subsumption_resolution,[],[f358,f77])).
% 1.98/0.64  fof(f77,plain,(
% 1.98/0.64    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f22])).
% 1.98/0.64  fof(f22,axiom,(
% 1.98/0.64    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.98/0.64  fof(f358,plain,(
% 1.98/0.64    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.98/0.64    inference(resolution,[],[f66,f107])).
% 1.98/0.64  fof(f107,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f57])).
% 1.98/0.64  fof(f57,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.64    inference(flattening,[],[f56])).
% 1.98/0.64  fof(f56,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.98/0.64    inference(ennf_transformation,[],[f20])).
% 1.98/0.64  fof(f20,axiom,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.98/0.64  fof(f66,plain,(
% 1.98/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f1233,plain,(
% 1.98/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1232,f64])).
% 1.98/0.64  fof(f1232,plain,(
% 1.98/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1231,f62])).
% 1.98/0.64  fof(f1231,plain,(
% 1.98/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1230,f73])).
% 1.98/0.64  fof(f1230,plain,(
% 1.98/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1229,f71])).
% 1.98/0.64  fof(f1229,plain,(
% 1.98/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.98/0.64    inference(superposition,[],[f110,f784])).
% 1.98/0.64  fof(f110,plain,(
% 1.98/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f61])).
% 1.98/0.64  fof(f61,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.98/0.64    inference(flattening,[],[f60])).
% 1.98/0.64  fof(f60,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.98/0.64    inference(ennf_transformation,[],[f21])).
% 1.98/0.64  fof(f21,axiom,(
% 1.98/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.98/0.64  fof(f785,plain,(
% 1.98/0.64    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.98/0.64    inference(backward_demodulation,[],[f66,f784])).
% 1.98/0.64  fof(f1448,plain,(
% 1.98/0.64    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f1447,f1260])).
% 1.98/0.64  fof(f1260,plain,(
% 1.98/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.98/0.64    inference(backward_demodulation,[],[f784,f1234])).
% 1.98/0.64  fof(f1447,plain,(
% 1.98/0.64    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1446,f73])).
% 1.98/0.64  fof(f1446,plain,(
% 1.98/0.64    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1445,f71])).
% 1.98/0.64  fof(f1445,plain,(
% 1.98/0.64    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.98/0.64    inference(resolution,[],[f198,f72])).
% 1.98/0.64  fof(f72,plain,(
% 1.98/0.64    v1_funct_2(sK2,sK0,sK1)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f198,plain,(
% 1.98/0.64    ( ! [X1] : (~v1_funct_2(X1,sK0,sK1) | ~v1_funct_1(X1) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0))) )),
% 1.98/0.64    inference(backward_demodulation,[],[f177,f184])).
% 1.98/0.64  fof(f184,plain,(
% 1.98/0.64    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 1.98/0.64    inference(resolution,[],[f64,f102])).
% 1.98/0.64  fof(f177,plain,(
% 1.98/0.64    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.98/0.64    inference(subsumption_resolution,[],[f176,f64])).
% 1.98/0.64  fof(f176,plain,(
% 1.98/0.64    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.98/0.64    inference(subsumption_resolution,[],[f173,f62])).
% 1.98/0.64  fof(f173,plain,(
% 1.98/0.64    ( ! [X1] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X1,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 1.98/0.64    inference(resolution,[],[f63,f105])).
% 1.98/0.64  fof(f105,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.98/0.64    inference(cnf_transformation,[],[f55])).
% 1.98/0.64  fof(f55,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.98/0.64    inference(flattening,[],[f54])).
% 1.98/0.64  fof(f54,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.98/0.64    inference(ennf_transformation,[],[f25])).
% 1.98/0.64  fof(f25,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.98/0.64  fof(f63,plain,(
% 1.98/0.64    v1_funct_2(sK3,sK1,sK0)),
% 1.98/0.64    inference(cnf_transformation,[],[f29])).
% 1.98/0.64  fof(f1572,plain,(
% 1.98/0.64    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1571,f62])).
% 1.98/0.64  fof(f1571,plain,(
% 1.98/0.64    ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.98/0.64    inference(subsumption_resolution,[],[f1557,f183])).
% 1.98/0.64  fof(f183,plain,(
% 1.98/0.64    v1_relat_1(sK3)),
% 1.98/0.64    inference(resolution,[],[f64,f101])).
% 1.98/0.64  fof(f1557,plain,(
% 1.98/0.64    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.98/0.64    inference(resolution,[],[f1554,f86])).
% 1.98/0.64  fof(f86,plain,(
% 1.98/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f38])).
% 1.98/0.64  fof(f38,plain,(
% 1.98/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.64    inference(flattening,[],[f37])).
% 1.98/0.64  fof(f37,plain,(
% 1.98/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.64    inference(ennf_transformation,[],[f14])).
% 1.98/0.64  fof(f14,axiom,(
% 1.98/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.98/0.64  fof(f1554,plain,(
% 1.98/0.64    v2_funct_1(sK3)),
% 1.98/0.64    inference(subsumption_resolution,[],[f1553,f276])).
% 1.98/0.64  fof(f1553,plain,(
% 1.98/0.64    sK1 != k2_relat_1(sK2) | v2_funct_1(sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f1552,f1269])).
% 1.98/0.64  fof(f1269,plain,(
% 1.98/0.64    sK1 = k1_relat_1(sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f1268,f429])).
% 1.98/0.64  fof(f429,plain,(
% 1.98/0.64    sK1 = k9_relat_1(sK2,sK0)),
% 1.98/0.64    inference(forward_demodulation,[],[f423,f276])).
% 1.98/0.64  fof(f423,plain,(
% 1.98/0.64    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 1.98/0.64    inference(superposition,[],[f302,f314])).
% 1.98/0.64  fof(f314,plain,(
% 1.98/0.64    sK2 = k7_relat_1(sK2,sK0)),
% 1.98/0.64    inference(subsumption_resolution,[],[f312,f261])).
% 1.98/0.64  fof(f312,plain,(
% 1.98/0.64    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 1.98/0.64    inference(resolution,[],[f263,f97])).
% 1.98/0.64  fof(f97,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.98/0.64    inference(cnf_transformation,[],[f50])).
% 1.98/0.64  fof(f50,plain,(
% 1.98/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(flattening,[],[f49])).
% 1.98/0.64  fof(f49,plain,(
% 1.98/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.98/0.64    inference(ennf_transformation,[],[f5])).
% 1.98/0.64  fof(f5,axiom,(
% 1.98/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.98/0.64  fof(f263,plain,(
% 1.98/0.64    v4_relat_1(sK2,sK0)),
% 1.98/0.64    inference(resolution,[],[f73,f103])).
% 1.98/0.64  fof(f103,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f53])).
% 1.98/0.64  fof(f53,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.64    inference(ennf_transformation,[],[f18])).
% 1.98/0.64  fof(f18,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.98/0.64  fof(f302,plain,(
% 1.98/0.64    ( ! [X10] : (k2_relat_1(k7_relat_1(sK2,X10)) = k9_relat_1(sK2,X10)) )),
% 1.98/0.64    inference(resolution,[],[f261,f92])).
% 1.98/0.64  fof(f92,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f43])).
% 1.98/0.64  fof(f43,plain,(
% 1.98/0.64    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(ennf_transformation,[],[f3])).
% 1.98/0.64  fof(f3,axiom,(
% 1.98/0.64    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.98/0.64  fof(f1268,plain,(
% 1.98/0.64    k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 1.98/0.64    inference(forward_demodulation,[],[f1259,f113])).
% 1.98/0.64  fof(f113,plain,(
% 1.98/0.64    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.98/0.64    inference(definition_unfolding,[],[f78,f75])).
% 1.98/0.64  fof(f78,plain,(
% 1.98/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f7])).
% 1.98/0.64  fof(f7,axiom,(
% 1.98/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.98/0.64  fof(f1259,plain,(
% 1.98/0.64    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))),
% 1.98/0.64    inference(backward_demodulation,[],[f537,f1234])).
% 1.98/0.64  fof(f537,plain,(
% 1.98/0.64    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 1.98/0.64    inference(backward_demodulation,[],[f430,f535])).
% 1.98/0.64  fof(f535,plain,(
% 1.98/0.64    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3))),
% 1.98/0.64    inference(resolution,[],[f205,f261])).
% 1.98/0.64  fof(f205,plain,(
% 1.98/0.64    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,sK3)) = k10_relat_1(X1,k1_relat_1(sK3))) )),
% 1.98/0.64    inference(resolution,[],[f183,f81])).
% 1.98/0.64  fof(f81,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f31])).
% 1.98/0.64  fof(f31,plain,(
% 1.98/0.64    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.98/0.64    inference(ennf_transformation,[],[f4])).
% 1.98/0.64  fof(f4,axiom,(
% 1.98/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.98/0.64  fof(f430,plain,(
% 1.98/0.64    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))),
% 1.98/0.64    inference(resolution,[],[f280,f230])).
% 1.98/0.64  fof(f230,plain,(
% 1.98/0.64    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.98/0.64    inference(subsumption_resolution,[],[f228,f183])).
% 1.98/0.64  fof(f228,plain,(
% 1.98/0.64    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),sK1)),
% 1.98/0.64    inference(resolution,[],[f185,f95])).
% 1.98/0.64  fof(f95,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f46])).
% 1.98/0.64  fof(f46,plain,(
% 1.98/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(ennf_transformation,[],[f2])).
% 1.98/0.64  fof(f2,axiom,(
% 1.98/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.98/0.64  fof(f185,plain,(
% 1.98/0.64    v4_relat_1(sK3,sK1)),
% 1.98/0.64    inference(resolution,[],[f64,f103])).
% 1.98/0.64  fof(f280,plain,(
% 1.98/0.64    ( ! [X4] : (~r1_tarski(X4,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4) )),
% 1.98/0.64    inference(subsumption_resolution,[],[f277,f261])).
% 1.98/0.64  fof(f277,plain,(
% 1.98/0.64    ( ! [X4] : (~r1_tarski(X4,sK1) | ~v1_relat_1(sK2) | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4) )),
% 1.98/0.64    inference(backward_demodulation,[],[f161,f276])).
% 1.98/0.64  fof(f161,plain,(
% 1.98/0.64    ( ! [X4] : (~v1_relat_1(sK2) | ~r1_tarski(X4,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X4)) = X4) )),
% 1.98/0.64    inference(resolution,[],[f71,f96])).
% 1.98/0.64  fof(f96,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f48])).
% 1.98/0.64  fof(f48,plain,(
% 1.98/0.64    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.98/0.64    inference(flattening,[],[f47])).
% 1.98/0.64  fof(f47,plain,(
% 1.98/0.64    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.98/0.64    inference(ennf_transformation,[],[f11])).
% 1.98/0.64  fof(f11,axiom,(
% 1.98/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.98/0.65  fof(f1552,plain,(
% 1.98/0.65    k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(subsumption_resolution,[],[f1551,f71])).
% 1.98/0.65  fof(f1551,plain,(
% 1.98/0.65    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(subsumption_resolution,[],[f1550,f261])).
% 1.98/0.65  fof(f1550,plain,(
% 1.98/0.65    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(subsumption_resolution,[],[f1549,f62])).
% 1.98/0.65  fof(f1549,plain,(
% 1.98/0.65    ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(subsumption_resolution,[],[f1548,f183])).
% 1.98/0.65  fof(f1548,plain,(
% 1.98/0.65    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(subsumption_resolution,[],[f1546,f111])).
% 1.98/0.65  fof(f111,plain,(
% 1.98/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f74,f75])).
% 1.98/0.65  fof(f74,plain,(
% 1.98/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f13])).
% 1.98/0.65  fof(f13,axiom,(
% 1.98/0.65    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.98/0.65  fof(f1546,plain,(
% 1.98/0.65    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | v2_funct_1(sK3)),
% 1.98/0.65    inference(superposition,[],[f91,f1234])).
% 1.98/0.65  fof(f91,plain,(
% 1.98/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X0)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f42])).
% 1.98/0.65  fof(f42,plain,(
% 1.98/0.65    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.65    inference(flattening,[],[f41])).
% 1.98/0.65  fof(f41,plain,(
% 1.98/0.65    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f12])).
% 1.98/0.65  fof(f12,axiom,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.98/0.65  fof(f250,plain,(
% 1.98/0.65    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 1.98/0.65    inference(resolution,[],[f203,f114])).
% 1.98/0.65  fof(f114,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.98/0.65    inference(definition_unfolding,[],[f80,f75])).
% 1.98/0.65  fof(f80,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.98/0.65    inference(cnf_transformation,[],[f30])).
% 1.98/0.65  fof(f30,plain,(
% 1.98/0.65    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.98/0.65    inference(ennf_transformation,[],[f8])).
% 1.98/0.65  fof(f8,axiom,(
% 1.98/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.98/0.65  fof(f203,plain,(
% 1.98/0.65    v1_relat_1(k2_funct_1(sK3))),
% 1.98/0.65    inference(resolution,[],[f183,f122])).
% 1.98/0.65  fof(f122,plain,(
% 1.98/0.65    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 1.98/0.65    inference(resolution,[],[f62,f83])).
% 1.98/0.65  fof(f83,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f34])).
% 1.98/0.65  fof(f34,plain,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.65    inference(flattening,[],[f33])).
% 1.98/0.65  fof(f33,plain,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f10])).
% 1.98/0.65  fof(f10,axiom,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.98/0.65  fof(f2159,plain,(
% 1.98/0.65    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 1.98/0.65    inference(forward_demodulation,[],[f2155,f1562])).
% 1.98/0.65  fof(f1562,plain,(
% 1.98/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.98/0.65    inference(forward_demodulation,[],[f1561,f1269])).
% 1.98/0.65  fof(f1561,plain,(
% 1.98/0.65    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.98/0.65    inference(subsumption_resolution,[],[f1560,f62])).
% 1.98/0.65  fof(f1560,plain,(
% 1.98/0.65    ~v1_funct_1(sK3) | k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.98/0.65    inference(subsumption_resolution,[],[f1555,f183])).
% 1.98/0.65  fof(f1555,plain,(
% 1.98/0.65    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.98/0.65    inference(resolution,[],[f1554,f116])).
% 1.98/0.65  fof(f116,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f88,f75])).
% 1.98/0.65  fof(f88,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f40])).
% 1.98/0.65  fof(f40,plain,(
% 1.98/0.65    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.65    inference(flattening,[],[f39])).
% 1.98/0.65  fof(f39,plain,(
% 1.98/0.65    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f15])).
% 1.98/0.65  fof(f15,axiom,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.98/0.65  fof(f2155,plain,(
% 1.98/0.65    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 1.98/0.65    inference(resolution,[],[f2092,f203])).
% 1.98/0.65  fof(f2092,plain,(
% 1.98/0.65    ( ! [X16] : (~v1_relat_1(X16) | k5_relat_1(sK2,k5_relat_1(sK3,X16)) = k5_relat_1(k6_partfun1(sK0),X16)) )),
% 1.98/0.65    inference(forward_demodulation,[],[f2089,f1234])).
% 1.98/0.65  fof(f2089,plain,(
% 1.98/0.65    ( ! [X16] : (~v1_relat_1(X16) | k5_relat_1(k5_relat_1(sK2,sK3),X16) = k5_relat_1(sK2,k5_relat_1(sK3,X16))) )),
% 1.98/0.65    inference(resolution,[],[f207,f261])).
% 1.98/0.65  fof(f207,plain,(
% 1.98/0.65    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,sK3),X5) = k5_relat_1(X4,k5_relat_1(sK3,X5))) )),
% 1.98/0.65    inference(resolution,[],[f183,f82])).
% 1.98/0.65  fof(f82,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f32])).
% 1.98/0.65  fof(f32,plain,(
% 1.98/0.65    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.98/0.65    inference(ennf_transformation,[],[f6])).
% 1.98/0.65  fof(f6,axiom,(
% 1.98/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.98/0.65  fof(f1583,plain,(
% 1.98/0.65    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.98/0.65    inference(subsumption_resolution,[],[f1582,f62])).
% 1.98/0.65  fof(f1582,plain,(
% 1.98/0.65    ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.98/0.65    inference(subsumption_resolution,[],[f1559,f183])).
% 1.98/0.65  fof(f1559,plain,(
% 1.98/0.65    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.98/0.65    inference(resolution,[],[f1554,f85])).
% 1.98/0.65  fof(f85,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.98/0.65    inference(cnf_transformation,[],[f36])).
% 1.98/0.65  fof(f36,plain,(
% 1.98/0.65    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.65    inference(flattening,[],[f35])).
% 1.98/0.65  fof(f35,plain,(
% 1.98/0.65    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f16])).
% 1.98/0.65  fof(f16,axiom,(
% 1.98/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.98/0.65  % SZS output end Proof for theBenchmark
% 1.98/0.65  % (32307)------------------------------
% 1.98/0.65  % (32307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.65  % (32307)Termination reason: Refutation
% 1.98/0.65  
% 1.98/0.65  % (32307)Memory used [KB]: 2814
% 1.98/0.65  % (32307)Time elapsed: 0.206 s
% 1.98/0.65  % (32307)------------------------------
% 1.98/0.65  % (32307)------------------------------
% 2.15/0.65  % (32289)Success in time 0.281 s
%------------------------------------------------------------------------------
