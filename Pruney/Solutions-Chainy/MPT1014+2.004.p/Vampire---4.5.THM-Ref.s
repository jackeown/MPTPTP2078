%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:24 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 542 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  389 (2794 expanded)
%              Number of equality atoms :  130 ( 444 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f495])).

fof(f495,plain,(
    k11_relat_1(sK2,sK3(sK0,sK2,sK2)) != k11_relat_1(sK2,sK3(sK0,sK2,sK2)) ),
    inference(backward_demodulation,[],[f165,f493])).

fof(f493,plain,(
    sK2 = k6_partfun1(sK0) ),
    inference(trivial_inequality_removal,[],[f489])).

fof(f489,plain,
    ( sK1 != sK1
    | sK2 = k6_partfun1(sK0) ),
    inference(superposition,[],[f300,f446])).

fof(f446,plain,(
    sK1 = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f445,f119])).

fof(f119,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f75])).

% (26757)Refutation not found, incomplete strategy% (26757)------------------------------
% (26757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26757)Termination reason: Refutation not found, incomplete strategy

% (26757)Memory used [KB]: 1663
% (26757)Time elapsed: 0.157 s
% (26757)------------------------------
% (26757)------------------------------
fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

fof(f445,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f443,f171])).

fof(f171,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f59,f75])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f443,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f442,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f442,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | sK1 = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f441,f233])).

fof(f233,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(superposition,[],[f135,f150])).

fof(f150,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f139,f131])).

fof(f131,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f121,f105])).

fof(f105,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f102,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f121,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f53,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f139,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f135,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,X0),sK0) ),
    inference(backward_demodulation,[],[f107,f122])).

fof(f122,plain,(
    ! [X4] : k7_relset_1(sK0,sK0,sK2,X4) = k9_relat_1(sK2,X4) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f107,plain,(
    ! [X0] : r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0) ) ),
    inference(resolution,[],[f52,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

fof(f441,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f440,f261])).

fof(f261,plain,(
    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f259,f150])).

fof(f259,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f209,f119])).

fof(f209,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK1,X0)) = k9_relat_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f196,f183])).

fof(f183,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f172,f55])).

fof(f55,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f172,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f196,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK1,X0)) = k9_relat_1(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f171,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f440,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f439,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f439,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0) ),
    inference(forward_demodulation,[],[f438,f243])).

fof(f243,plain,(
    sK0 = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f241,f206])).

fof(f206,plain,(
    sK0 = k10_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f205,f187])).

fof(f187,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f173,f111])).

fof(f111,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f59])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f108,f57])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f58,f69])).

fof(f58,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f173,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f59,f77])).

fof(f205,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f194,f183])).

fof(f194,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f171,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f241,plain,(
    k10_relat_1(sK1,sK0) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f151,f171])).

fof(f151,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X3,sK2)) = k10_relat_1(X3,sK0) ) ),
    inference(forward_demodulation,[],[f143,f131])).

fof(f143,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X3,sK2)) = k10_relat_1(X3,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f119,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f438,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),sK0)
    | ~ r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0) ),
    inference(resolution,[],[f425,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f425,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k5_relat_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f422,f420])).

fof(f420,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f418,f57])).

fof(f418,plain,
    ( ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(resolution,[],[f137,f59])).

fof(f137,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(X12)
      | k1_partfun1(X13,X14,sK0,sK0,X12,sK2) = k5_relat_1(X12,sK2) ) ),
    inference(subsumption_resolution,[],[f129,f51])).

fof(f129,plain,(
    ! [X14,X12,X13] :
      ( ~ v1_funct_1(X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(sK2)
      | k1_partfun1(X13,X14,sK0,sK0,X12,sK2) = k5_relat_1(X12,sK2) ) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f422,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f225,f420])).

fof(f225,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f222,f59])).

fof(f222,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(resolution,[],[f54,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f300,plain,
    ( sK1 != k5_relat_1(sK1,sK2)
    | sK2 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f299,f183])).

fof(f299,plain,
    ( sK2 = k6_partfun1(sK0)
    | sK0 != k2_relat_1(sK1)
    | sK1 != k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f297,f171])).

fof(f297,plain,
    ( sK2 = k6_partfun1(sK0)
    | ~ v1_relat_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | sK1 != k5_relat_1(sK1,sK2) ),
    inference(resolution,[],[f134,f57])).

fof(f134,plain,(
    ! [X8] :
      ( ~ v1_funct_1(X8)
      | sK2 = k6_partfun1(sK0)
      | ~ v1_relat_1(X8)
      | sK0 != k2_relat_1(X8)
      | k5_relat_1(X8,sK2) != X8 ) ),
    inference(forward_demodulation,[],[f133,f131])).

fof(f133,plain,(
    ! [X8] :
      ( sK2 = k6_partfun1(sK0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k2_relat_1(X8) != k1_relat_1(sK2)
      | k5_relat_1(X8,sK2) != X8 ) ),
    inference(subsumption_resolution,[],[f132,f119])).

fof(f132,plain,(
    ! [X8] :
      ( sK2 = k6_partfun1(sK0)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(X8) != k1_relat_1(sK2)
      | k5_relat_1(X8,sK2) != X8 ) ),
    inference(backward_demodulation,[],[f94,f131])).

fof(f94,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(sK2)
      | k2_relat_1(X8) != k1_relat_1(sK2)
      | k5_relat_1(X8,sK2) != X8
      | sK2 = k6_partfun1(k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f51,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f165,plain,(
    k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0))) ),
    inference(subsumption_resolution,[],[f164,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f164,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0))) ),
    inference(subsumption_resolution,[],[f162,f53])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0))) ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k11_relat_1(X1,sK3(X0,X1,X2)) != k11_relat_1(X2,sK3(X0,X1,X2))
      | r2_relset_1(X0,X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

fof(f56,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (26734)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (26727)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (26745)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (26735)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (26746)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (26728)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (26728)Refutation not found, incomplete strategy% (26728)------------------------------
% 0.21/0.53  % (26728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26728)Memory used [KB]: 1791
% 0.21/0.53  % (26728)Time elapsed: 0.109 s
% 0.21/0.53  % (26728)------------------------------
% 0.21/0.53  % (26728)------------------------------
% 0.21/0.53  % (26729)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (26730)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.54  % (26731)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.54  % (26742)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.54  % (26746)Refutation not found, incomplete strategy% (26746)------------------------------
% 1.38/0.54  % (26746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (26746)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (26746)Memory used [KB]: 1791
% 1.38/0.54  % (26746)Time elapsed: 0.125 s
% 1.38/0.54  % (26746)------------------------------
% 1.38/0.54  % (26746)------------------------------
% 1.38/0.54  % (26753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.54  % (26740)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.54  % (26732)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.54  % (26751)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (26756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.54  % (26755)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.55  % (26752)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.55  % (26750)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (26739)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.55  % (26749)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (26744)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (26748)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.55  % (26754)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (26745)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % (26739)Refutation not found, incomplete strategy% (26739)------------------------------
% 1.38/0.55  % (26739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26744)Refutation not found, incomplete strategy% (26744)------------------------------
% 1.38/0.55  % (26744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (26738)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.56  % (26741)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (26747)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.56  % (26737)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (26736)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.56  % (26733)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (26757)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f501,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f495])).
% 1.48/0.56  fof(f495,plain,(
% 1.48/0.56    k11_relat_1(sK2,sK3(sK0,sK2,sK2)) != k11_relat_1(sK2,sK3(sK0,sK2,sK2))),
% 1.48/0.56    inference(backward_demodulation,[],[f165,f493])).
% 1.48/0.56  fof(f493,plain,(
% 1.48/0.56    sK2 = k6_partfun1(sK0)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f489])).
% 1.48/0.56  fof(f489,plain,(
% 1.48/0.56    sK1 != sK1 | sK2 = k6_partfun1(sK0)),
% 1.48/0.56    inference(superposition,[],[f300,f446])).
% 1.48/0.56  fof(f446,plain,(
% 1.48/0.56    sK1 = k5_relat_1(sK1,sK2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f445,f119])).
% 1.48/0.56  fof(f119,plain,(
% 1.48/0.56    v1_relat_1(sK2)),
% 1.48/0.56    inference(resolution,[],[f53,f75])).
% 1.48/0.56  % (26757)Refutation not found, incomplete strategy% (26757)------------------------------
% 1.48/0.56  % (26757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (26757)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (26757)Memory used [KB]: 1663
% 1.48/0.56  % (26757)Time elapsed: 0.157 s
% 1.48/0.56  % (26757)------------------------------
% 1.48/0.56  % (26757)------------------------------
% 1.48/0.56  fof(f75,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f39])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.48/0.56    inference(flattening,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.48/0.56    inference(negated_conjecture,[],[f21])).
% 1.48/0.56  fof(f21,conjecture,(
% 1.48/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).
% 1.48/0.56  fof(f445,plain,(
% 1.48/0.56    sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(sK2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f443,f171])).
% 1.48/0.56  fof(f171,plain,(
% 1.48/0.56    v1_relat_1(sK1)),
% 1.48/0.56    inference(resolution,[],[f59,f75])).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f443,plain,(
% 1.48/0.56    sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)),
% 1.48/0.56    inference(resolution,[],[f442,f70])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.48/0.56  fof(f442,plain,(
% 1.48/0.56    ~v1_relat_1(k5_relat_1(sK1,sK2)) | sK1 = k5_relat_1(sK1,sK2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f441,f233])).
% 1.48/0.56  fof(f233,plain,(
% 1.48/0.56    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.48/0.56    inference(superposition,[],[f135,f150])).
% 1.48/0.56  fof(f150,plain,(
% 1.48/0.56    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 1.48/0.56    inference(forward_demodulation,[],[f139,f131])).
% 1.48/0.56  fof(f131,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK2)),
% 1.48/0.56    inference(forward_demodulation,[],[f121,f105])).
% 1.48/0.56  fof(f105,plain,(
% 1.48/0.56    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f104,f53])).
% 1.48/0.56  fof(f104,plain,(
% 1.48/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.48/0.56    inference(subsumption_resolution,[],[f102,f51])).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    v1_funct_1(sK2)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f102,plain,(
% 1.48/0.56    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.48/0.56    inference(resolution,[],[f52,f69])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.48/0.56    inference(flattening,[],[f33])).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f20])).
% 1.48/0.56  fof(f20,axiom,(
% 1.48/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.48/0.56  fof(f52,plain,(
% 1.48/0.56    v1_funct_2(sK2,sK0,sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f121,plain,(
% 1.48/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 1.48/0.56    inference(resolution,[],[f53,f77])).
% 1.48/0.56  fof(f77,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f41])).
% 1.48/0.56  fof(f41,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.56  fof(f139,plain,(
% 1.48/0.56    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.48/0.56    inference(resolution,[],[f119,f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.48/0.56  fof(f135,plain,(
% 1.48/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),sK0)) )),
% 1.48/0.56    inference(backward_demodulation,[],[f107,f122])).
% 1.48/0.56  fof(f122,plain,(
% 1.48/0.56    ( ! [X4] : (k7_relset_1(sK0,sK0,sK2,X4) = k9_relat_1(sK2,X4)) )),
% 1.48/0.56    inference(resolution,[],[f53,f78])).
% 1.48/0.56  fof(f78,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f42])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.48/0.56  fof(f107,plain,(
% 1.48/0.56    ( ! [X0] : (r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f106,f53])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f103,f51])).
% 1.48/0.56  fof(f103,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r1_tarski(k7_relset_1(sK0,sK0,sK2,X0),sK0)) )),
% 1.48/0.56    inference(resolution,[],[f52,f79])).
% 1.48/0.56  fof(f79,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f44])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.48/0.56    inference(flattening,[],[f43])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.48/0.56    inference(ennf_transformation,[],[f19])).
% 1.48/0.56  fof(f19,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).
% 1.48/0.56  fof(f441,plain,(
% 1.48/0.56    ~r1_tarski(k2_relat_1(sK2),sK0) | sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(k5_relat_1(sK1,sK2))),
% 1.48/0.56    inference(forward_demodulation,[],[f440,f261])).
% 1.48/0.56  fof(f261,plain,(
% 1.48/0.56    k2_relat_1(sK2) = k2_relat_1(k5_relat_1(sK1,sK2))),
% 1.48/0.56    inference(forward_demodulation,[],[f259,f150])).
% 1.48/0.56  fof(f259,plain,(
% 1.48/0.56    k9_relat_1(sK2,sK0) = k2_relat_1(k5_relat_1(sK1,sK2))),
% 1.48/0.56    inference(resolution,[],[f209,f119])).
% 1.48/0.56  fof(f209,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK1,X0)) = k9_relat_1(X0,sK0)) )),
% 1.48/0.56    inference(forward_demodulation,[],[f196,f183])).
% 1.48/0.56  fof(f183,plain,(
% 1.48/0.56    sK0 = k2_relat_1(sK1)),
% 1.48/0.56    inference(forward_demodulation,[],[f172,f55])).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f172,plain,(
% 1.48/0.56    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.48/0.56    inference(resolution,[],[f59,f76])).
% 1.48/0.56  fof(f76,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f40])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.56  fof(f196,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK1,X0)) = k9_relat_1(X0,k2_relat_1(sK1))) )),
% 1.48/0.56    inference(resolution,[],[f171,f64])).
% 1.48/0.56  fof(f64,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f27])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.48/0.56  fof(f440,plain,(
% 1.48/0.56    sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(k5_relat_1(sK1,sK2)) | ~r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f439,f87])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f71])).
% 1.48/0.56  fof(f71,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.56  fof(f439,plain,(
% 1.48/0.56    ~r1_tarski(sK0,sK0) | sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(k5_relat_1(sK1,sK2)) | ~r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0)),
% 1.48/0.56    inference(forward_demodulation,[],[f438,f243])).
% 1.48/0.56  fof(f243,plain,(
% 1.48/0.56    sK0 = k1_relat_1(k5_relat_1(sK1,sK2))),
% 1.48/0.56    inference(forward_demodulation,[],[f241,f206])).
% 1.48/0.56  fof(f206,plain,(
% 1.48/0.56    sK0 = k10_relat_1(sK1,sK0)),
% 1.48/0.56    inference(forward_demodulation,[],[f205,f187])).
% 1.48/0.56  fof(f187,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK1)),
% 1.48/0.56    inference(forward_demodulation,[],[f173,f111])).
% 1.48/0.56  fof(f111,plain,(
% 1.48/0.56    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f110,f59])).
% 1.48/0.56  fof(f110,plain,(
% 1.48/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f108,f57])).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    v1_funct_1(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.48/0.56    inference(resolution,[],[f58,f69])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f173,plain,(
% 1.48/0.56    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.48/0.56    inference(resolution,[],[f59,f77])).
% 1.48/0.56  fof(f205,plain,(
% 1.48/0.56    k1_relat_1(sK1) = k10_relat_1(sK1,sK0)),
% 1.48/0.56    inference(forward_demodulation,[],[f194,f183])).
% 1.48/0.56  fof(f194,plain,(
% 1.48/0.56    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.48/0.56    inference(resolution,[],[f171,f62])).
% 1.48/0.56  fof(f62,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.48/0.56  fof(f241,plain,(
% 1.48/0.56    k10_relat_1(sK1,sK0) = k1_relat_1(k5_relat_1(sK1,sK2))),
% 1.48/0.56    inference(resolution,[],[f151,f171])).
% 1.48/0.56  fof(f151,plain,(
% 1.48/0.56    ( ! [X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X3,sK2)) = k10_relat_1(X3,sK0)) )),
% 1.48/0.56    inference(forward_demodulation,[],[f143,f131])).
% 1.48/0.56  fof(f143,plain,(
% 1.48/0.56    ( ! [X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X3,sK2)) = k10_relat_1(X3,k1_relat_1(sK2))) )),
% 1.48/0.56    inference(resolution,[],[f119,f65])).
% 1.48/0.56  fof(f65,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.48/0.56  fof(f438,plain,(
% 1.48/0.56    sK1 = k5_relat_1(sK1,sK2) | ~v1_relat_1(k5_relat_1(sK1,sK2)) | ~r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),sK0) | ~r1_tarski(k2_relat_1(k5_relat_1(sK1,sK2)),sK0)),
% 1.48/0.56    inference(resolution,[],[f425,f74])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.48/0.56    inference(flattening,[],[f37])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.48/0.57  fof(f425,plain,(
% 1.48/0.57    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k5_relat_1(sK1,sK2)),
% 1.48/0.57    inference(forward_demodulation,[],[f422,f420])).
% 1.48/0.57  fof(f420,plain,(
% 1.48/0.57    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f418,f57])).
% 1.48/0.57  fof(f418,plain,(
% 1.48/0.57    ~v1_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 1.48/0.57    inference(resolution,[],[f137,f59])).
% 1.48/0.57  fof(f137,plain,(
% 1.48/0.57    ( ! [X14,X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(X12) | k1_partfun1(X13,X14,sK0,sK0,X12,sK2) = k5_relat_1(X12,sK2)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f129,f51])).
% 1.48/0.57  fof(f129,plain,(
% 1.48/0.57    ( ! [X14,X12,X13] : (~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(sK2) | k1_partfun1(X13,X14,sK0,sK0,X12,sK2) = k5_relat_1(X12,sK2)) )),
% 1.48/0.57    inference(resolution,[],[f53,f83])).
% 1.48/0.57  fof(f83,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f50])).
% 1.48/0.57  fof(f50,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.57    inference(flattening,[],[f49])).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.57    inference(ennf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.48/0.57  fof(f422,plain,(
% 1.48/0.57    sK1 = k5_relat_1(sK1,sK2) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.57    inference(backward_demodulation,[],[f225,f420])).
% 1.48/0.57  fof(f225,plain,(
% 1.48/0.57    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f222,f59])).
% 1.48/0.57  fof(f222,plain,(
% 1.48/0.57    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.48/0.57    inference(resolution,[],[f54,f82])).
% 1.48/0.57  fof(f82,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f48])).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(flattening,[],[f47])).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.57    inference(ennf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.48/0.57  fof(f54,plain,(
% 1.48/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.48/0.57    inference(cnf_transformation,[],[f24])).
% 1.48/0.57  fof(f300,plain,(
% 1.48/0.57    sK1 != k5_relat_1(sK1,sK2) | sK2 = k6_partfun1(sK0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f299,f183])).
% 1.48/0.57  fof(f299,plain,(
% 1.48/0.57    sK2 = k6_partfun1(sK0) | sK0 != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f297,f171])).
% 1.48/0.57  fof(f297,plain,(
% 1.48/0.57    sK2 = k6_partfun1(sK0) | ~v1_relat_1(sK1) | sK0 != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,sK2)),
% 1.48/0.57    inference(resolution,[],[f134,f57])).
% 1.48/0.57  fof(f134,plain,(
% 1.48/0.57    ( ! [X8] : (~v1_funct_1(X8) | sK2 = k6_partfun1(sK0) | ~v1_relat_1(X8) | sK0 != k2_relat_1(X8) | k5_relat_1(X8,sK2) != X8) )),
% 1.48/0.57    inference(forward_demodulation,[],[f133,f131])).
% 1.48/0.57  fof(f133,plain,(
% 1.48/0.57    ( ! [X8] : (sK2 = k6_partfun1(sK0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | k2_relat_1(X8) != k1_relat_1(sK2) | k5_relat_1(X8,sK2) != X8) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f132,f119])).
% 1.48/0.57  fof(f132,plain,(
% 1.48/0.57    ( ! [X8] : (sK2 = k6_partfun1(sK0) | ~v1_relat_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(sK2) | k2_relat_1(X8) != k1_relat_1(sK2) | k5_relat_1(X8,sK2) != X8) )),
% 1.48/0.57    inference(backward_demodulation,[],[f94,f131])).
% 1.48/0.57  fof(f94,plain,(
% 1.48/0.57    ( ! [X8] : (~v1_relat_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(sK2) | k2_relat_1(X8) != k1_relat_1(sK2) | k5_relat_1(X8,sK2) != X8 | sK2 = k6_partfun1(k1_relat_1(sK2))) )),
% 1.48/0.57    inference(resolution,[],[f51,f85])).
% 1.48/0.57  fof(f85,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 1.48/0.57    inference(definition_unfolding,[],[f66,f60])).
% 1.48/0.57  fof(f60,plain,(
% 1.48/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,axiom,(
% 1.48/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.48/0.57  fof(f66,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f30])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(flattening,[],[f29])).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 1.48/0.57  fof(f165,plain,(
% 1.48/0.57    k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0)))),
% 1.48/0.57    inference(subsumption_resolution,[],[f164,f84])).
% 1.48/0.57  fof(f84,plain,(
% 1.48/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f61,f60])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f15])).
% 1.48/0.57  fof(f15,axiom,(
% 1.48/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.48/0.57  fof(f164,plain,(
% 1.48/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0)))),
% 1.48/0.57    inference(subsumption_resolution,[],[f162,f53])).
% 1.48/0.57  fof(f162,plain,(
% 1.48/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k11_relat_1(sK2,sK3(sK0,sK2,k6_partfun1(sK0))) != k11_relat_1(k6_partfun1(sK0),sK3(sK0,sK2,k6_partfun1(sK0)))),
% 1.48/0.57    inference(resolution,[],[f56,f68])).
% 1.48/0.57  fof(f68,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k11_relat_1(X1,sK3(X0,X1,X2)) != k11_relat_1(X2,sK3(X0,X1,X2)) | r2_relset_1(X0,X0,X1,X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.48/0.57    inference(flattening,[],[f31])).
% 1.48/0.57  fof(f31,plain,(
% 1.48/0.57    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.48/0.57    inference(ennf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).
% 1.48/0.57  fof(f56,plain,(
% 1.48/0.57    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.48/0.57    inference(cnf_transformation,[],[f24])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (26745)------------------------------
% 1.48/0.57  % (26745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (26745)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (26745)Memory used [KB]: 2046
% 1.48/0.57  % (26745)Time elapsed: 0.134 s
% 1.48/0.57  % (26745)------------------------------
% 1.48/0.57  % (26745)------------------------------
% 1.48/0.57  % (26725)Success in time 0.204 s
%------------------------------------------------------------------------------
