%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 (1070 expanded)
%              Number of leaves         :   19 ( 204 expanded)
%              Depth                    :   22
%              Number of atoms          :  480 (6388 expanded)
%              Number of equality atoms :   93 ( 452 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1078,f160])).

fof(f160,plain,(
    ! [X2,X3] : r2_relset_1(X2,X3,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f154,f138])).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f137,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f136,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f68,f67])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f135,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(resolution,[],[f89,f69])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1078,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f941,f1032])).

fof(f1032,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f795,f255])).

fof(f255,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f96,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f146,f69])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f145,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f55])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f795,plain,(
    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f688,f736])).

fof(f736,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f655,f255])).

fof(f655,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f571,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f571,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f93,f563])).

fof(f563,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f542,f152])).

fof(f152,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f89,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f542,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f278,f513])).

fof(f513,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f512,f51])).

fof(f51,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f512,plain,
    ( ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f511,f212])).

fof(f212,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f174,f211])).

fof(f211,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f210,f105])).

fof(f105,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f210,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f209,f122])).

fof(f122,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f76,f54])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f209,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f208,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f208,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f207,f54])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f199,f53])).

fof(f53,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f199,plain,(
    ! [X2,X3] :
      ( ~ v3_funct_2(sK1,X2,X3)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v2_funct_2(sK1,X3) ) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f174,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f511,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f510,f48])).

fof(f510,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f509,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f509,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f508,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f508,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f507,f54])).

fof(f507,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f506,f52])).

fof(f52,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f506,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(resolution,[],[f90,f49])).

fof(f49,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_funct_1(X2) = X3 ) ),
    inference(subsumption_resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_funct_1(X2) = X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

% (32584)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f278,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f50,f277])).

fof(f277,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f276,f54])).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f275,f53])).

fof(f275,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f260,f51])).

fof(f260,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f61,f52])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f688,plain,(
    r1_tarski(k2_funct_1(sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f617,f86])).

fof(f617,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f405,f563])).

fof(f405,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f392,f70])).

fof(f392,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f391,f263])).

fof(f263,plain,(
    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f262,f48])).

fof(f262,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f47])).

fof(f47,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f261,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f259,f45])).

fof(f259,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f61,f46])).

fof(f391,plain,(
    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f390,f48])).

fof(f390,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f389,f47])).

fof(f389,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f380,f46])).

fof(f380,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,X0,X0)
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f941,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f773,f878])).

fof(f878,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f656,f255])).

fof(f656,plain,(
    r1_tarski(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f572,f86])).

fof(f572,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f94,f563])).

fof(f94,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f70,f54])).

fof(f773,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f593,f736])).

fof(f593,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f278,f563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:12:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (32596)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (32588)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (32580)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (32589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (32597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (32581)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.55  % (32578)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.55  % (32580)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % (32576)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.55  % (32600)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.56  % (32594)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.57  % SZS output start Proof for theBenchmark
% 0.19/0.57  fof(f1142,plain,(
% 0.19/0.57    $false),
% 0.19/0.57    inference(subsumption_resolution,[],[f1078,f160])).
% 0.19/0.57  fof(f160,plain,(
% 0.19/0.57    ( ! [X2,X3] : (r2_relset_1(X2,X3,k1_xboole_0,k1_xboole_0)) )),
% 0.19/0.57    inference(resolution,[],[f154,f138])).
% 0.19/0.57  fof(f138,plain,(
% 0.19/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.57    inference(resolution,[],[f137,f67])).
% 0.19/0.57  fof(f67,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f32])).
% 0.19/0.57  fof(f32,plain,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.57    inference(ennf_transformation,[],[f1])).
% 0.19/0.57  fof(f1,axiom,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.57  fof(f137,plain,(
% 0.19/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.57    inference(resolution,[],[f136,f102])).
% 0.19/0.57  fof(f102,plain,(
% 0.19/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f101])).
% 0.19/0.57  fof(f101,plain,(
% 0.19/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.19/0.57    inference(resolution,[],[f68,f67])).
% 0.19/0.57  fof(f68,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f32])).
% 0.19/0.57  fof(f136,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.57    inference(resolution,[],[f135,f69])).
% 0.19/0.57  fof(f69,plain,(
% 0.19/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f5])).
% 0.19/0.57  fof(f5,axiom,(
% 0.19/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.57  fof(f135,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 0.19/0.57    inference(resolution,[],[f82,f55])).
% 0.19/0.57  fof(f55,plain,(
% 0.19/0.57    v1_xboole_0(k1_xboole_0)),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    v1_xboole_0(k1_xboole_0)),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.57  fof(f82,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f42])).
% 0.19/0.57  fof(f42,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f6])).
% 0.19/0.57  fof(f6,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.57  fof(f154,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.19/0.57    inference(resolution,[],[f89,f69])).
% 0.19/0.57  fof(f89,plain,(
% 0.19/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f88])).
% 0.19/0.57  fof(f88,plain,(
% 0.19/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.57    inference(equality_resolution,[],[f83])).
% 0.19/0.57  fof(f83,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f44])).
% 0.19/0.57  fof(f44,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(flattening,[],[f43])).
% 0.19/0.57  fof(f43,plain,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.57    inference(ennf_transformation,[],[f12])).
% 0.19/0.57  fof(f12,axiom,(
% 0.19/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.57  fof(f1078,plain,(
% 0.19/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.57    inference(backward_demodulation,[],[f941,f1032])).
% 0.19/0.57  fof(f1032,plain,(
% 0.19/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.19/0.57    inference(resolution,[],[f795,f255])).
% 0.19/0.57  fof(f255,plain,(
% 0.19/0.57    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.19/0.57    inference(global_subsumption,[],[f96,f147])).
% 0.19/0.57  fof(f147,plain,(
% 0.19/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.19/0.57    inference(resolution,[],[f146,f69])).
% 0.19/0.57  fof(f146,plain,(
% 0.19/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.19/0.57    inference(forward_demodulation,[],[f145,f87])).
% 0.19/0.57  fof(f87,plain,(
% 0.19/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.57    inference(equality_resolution,[],[f72])).
% 0.19/0.57  fof(f72,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.57  fof(f145,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) )),
% 0.19/0.57    inference(resolution,[],[f58,f55])).
% 0.19/0.57  fof(f58,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f25])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f10])).
% 0.19/0.57  fof(f10,axiom,(
% 0.19/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.19/0.57  fof(f96,plain,(
% 0.19/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.57    inference(resolution,[],[f74,f55])).
% 0.19/0.57  fof(f74,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f33])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f3])).
% 0.19/0.57  fof(f3,axiom,(
% 0.19/0.57    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.19/0.57  fof(f795,plain,(
% 0.19/0.57    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)),
% 0.19/0.57    inference(backward_demodulation,[],[f688,f736])).
% 0.19/0.57  fof(f736,plain,(
% 0.19/0.57    k1_xboole_0 = sK2),
% 0.19/0.57    inference(resolution,[],[f655,f255])).
% 0.19/0.57  fof(f655,plain,(
% 0.19/0.57    r1_tarski(sK2,k1_xboole_0)),
% 0.19/0.57    inference(forward_demodulation,[],[f571,f86])).
% 0.19/0.57  fof(f86,plain,(
% 0.19/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.57    inference(equality_resolution,[],[f73])).
% 0.19/0.57  fof(f73,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f4])).
% 0.19/0.57  fof(f571,plain,(
% 0.19/0.57    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 0.19/0.57    inference(backward_demodulation,[],[f93,f563])).
% 0.19/0.57  fof(f563,plain,(
% 0.19/0.57    k1_xboole_0 = sK0),
% 0.19/0.57    inference(subsumption_resolution,[],[f542,f152])).
% 0.19/0.57  fof(f152,plain,(
% 0.19/0.57    r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.19/0.57    inference(resolution,[],[f89,f48])).
% 0.19/0.57  fof(f48,plain,(
% 0.19/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f23,plain,(
% 0.19/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.57    inference(flattening,[],[f22])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f20])).
% 0.19/0.57  fof(f20,negated_conjecture,(
% 0.19/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.19/0.57    inference(negated_conjecture,[],[f19])).
% 0.19/0.57  fof(f19,conjecture,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 0.19/0.57  fof(f542,plain,(
% 0.19/0.57    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 0.19/0.57    inference(superposition,[],[f278,f513])).
% 0.19/0.57  fof(f513,plain,(
% 0.19/0.57    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.19/0.57    inference(subsumption_resolution,[],[f512,f51])).
% 0.19/0.57  fof(f51,plain,(
% 0.19/0.57    v1_funct_1(sK1)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f512,plain,(
% 0.19/0.57    ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f511,f212])).
% 0.19/0.57  fof(f212,plain,(
% 0.19/0.57    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.19/0.57    inference(backward_demodulation,[],[f174,f211])).
% 0.19/0.57  fof(f211,plain,(
% 0.19/0.57    sK0 = k2_relat_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f210,f105])).
% 0.19/0.57  fof(f105,plain,(
% 0.19/0.57    v1_relat_1(sK1)),
% 0.19/0.57    inference(resolution,[],[f98,f54])).
% 0.19/0.57  fof(f54,plain,(
% 0.19/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f98,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.19/0.57    inference(resolution,[],[f56,f57])).
% 0.19/0.57  fof(f57,plain,(
% 0.19/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  fof(f8,axiom,(
% 0.19/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.57  fof(f56,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f24])).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f7])).
% 0.19/0.57  fof(f7,axiom,(
% 0.19/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.57  fof(f210,plain,(
% 0.19/0.57    sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f209,f122])).
% 0.19/0.57  fof(f122,plain,(
% 0.19/0.57    v5_relat_1(sK1,sK0)),
% 0.19/0.57    inference(resolution,[],[f76,f54])).
% 0.19/0.57  fof(f76,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f35])).
% 0.19/0.57  fof(f35,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.57    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.57  fof(f9,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.57  fof(f209,plain,(
% 0.19/0.57    ~v5_relat_1(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.57    inference(resolution,[],[f208,f60])).
% 0.19/0.57  fof(f60,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.57    inference(flattening,[],[f26])).
% 0.19/0.57  fof(f26,plain,(
% 0.19/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,axiom,(
% 0.19/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.57  fof(f208,plain,(
% 0.19/0.57    v2_funct_2(sK1,sK0)),
% 0.19/0.57    inference(subsumption_resolution,[],[f207,f54])).
% 0.19/0.57  fof(f207,plain,(
% 0.19/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v2_funct_2(sK1,sK0)),
% 0.19/0.57    inference(resolution,[],[f199,f53])).
% 0.19/0.57  fof(f53,plain,(
% 0.19/0.57    v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f199,plain,(
% 0.19/0.57    ( ! [X2,X3] : (~v3_funct_2(sK1,X2,X3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v2_funct_2(sK1,X3)) )),
% 0.19/0.57    inference(resolution,[],[f78,f51])).
% 0.19/0.57  fof(f78,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f37])).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(flattening,[],[f36])).
% 0.19/0.57  fof(f36,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f13])).
% 0.19/0.57  fof(f13,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.19/0.57  fof(f174,plain,(
% 0.19/0.57    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 0.19/0.57    inference(resolution,[],[f75,f54])).
% 0.19/0.57  fof(f75,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f34])).
% 0.19/0.57  fof(f34,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.57    inference(ennf_transformation,[],[f11])).
% 0.19/0.57  fof(f11,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.57  fof(f511,plain,(
% 0.19/0.57    sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f510,f48])).
% 0.19/0.57  fof(f510,plain,(
% 0.19/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f509,f46])).
% 0.19/0.57  fof(f46,plain,(
% 0.19/0.57    v1_funct_2(sK2,sK0,sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f509,plain,(
% 0.19/0.57    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f508,f45])).
% 0.19/0.57  fof(f45,plain,(
% 0.19/0.57    v1_funct_1(sK2)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f508,plain,(
% 0.19/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f507,f54])).
% 0.19/0.57  fof(f507,plain,(
% 0.19/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f506,f52])).
% 0.19/0.57  fof(f52,plain,(
% 0.19/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f506,plain,(
% 0.19/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f505])).
% 0.19/0.57  fof(f505,plain,(
% 0.19/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 0.19/0.57    inference(resolution,[],[f90,f49])).
% 0.19/0.57  fof(f49,plain,(
% 0.19/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f90,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f81,f79])).
% 0.19/0.57  fof(f79,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f39])).
% 0.19/0.57  fof(f39,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f38])).
% 0.19/0.57  fof(f38,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f17])).
% 0.19/0.57  fof(f17,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.19/0.57  fof(f81,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v2_funct_1(X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_funct_1(X2) = X3) )),
% 0.19/0.57    inference(cnf_transformation,[],[f41])).
% 0.19/0.57  fof(f41,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f40])).
% 0.19/0.57  % (32584)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.57  fof(f40,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f18])).
% 0.19/0.57  fof(f18,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.19/0.57  fof(f278,plain,(
% 0.19/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 0.19/0.57    inference(backward_demodulation,[],[f50,f277])).
% 0.19/0.57  fof(f277,plain,(
% 0.19/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f276,f54])).
% 0.19/0.57  fof(f276,plain,(
% 0.19/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f275,f53])).
% 0.19/0.57  fof(f275,plain,(
% 0.19/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.19/0.57    inference(subsumption_resolution,[],[f260,f51])).
% 0.19/0.57  fof(f260,plain,(
% 0.19/0.57    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.19/0.57    inference(resolution,[],[f61,f52])).
% 0.19/0.57  fof(f61,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f29])).
% 0.19/0.57  fof(f29,plain,(
% 0.19/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.57    inference(flattening,[],[f28])).
% 0.19/0.57  fof(f28,plain,(
% 0.19/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f16])).
% 0.19/0.57  fof(f16,axiom,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.19/0.57  fof(f50,plain,(
% 0.19/0.57    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f93,plain,(
% 0.19/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK0))),
% 0.19/0.57    inference(resolution,[],[f70,f48])).
% 0.19/0.57  fof(f70,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f5])).
% 0.19/0.57  fof(f688,plain,(
% 0.19/0.57    r1_tarski(k2_funct_1(sK2),k1_xboole_0)),
% 0.19/0.57    inference(forward_demodulation,[],[f617,f86])).
% 0.19/0.57  fof(f617,plain,(
% 0.19/0.57    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 0.19/0.57    inference(backward_demodulation,[],[f405,f563])).
% 0.19/0.57  fof(f405,plain,(
% 0.19/0.57    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.57    inference(resolution,[],[f392,f70])).
% 0.19/0.57  fof(f392,plain,(
% 0.19/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(forward_demodulation,[],[f391,f263])).
% 0.19/0.57  fof(f263,plain,(
% 0.19/0.57    k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.19/0.57    inference(subsumption_resolution,[],[f262,f48])).
% 0.19/0.57  fof(f262,plain,(
% 0.19/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.19/0.57    inference(subsumption_resolution,[],[f261,f47])).
% 0.19/0.57  fof(f47,plain,(
% 0.19/0.57    v3_funct_2(sK2,sK0,sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f261,plain,(
% 0.19/0.57    ~v3_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.19/0.57    inference(subsumption_resolution,[],[f259,f45])).
% 0.19/0.57  fof(f259,plain,(
% 0.19/0.57    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 0.19/0.57    inference(resolution,[],[f61,f46])).
% 0.19/0.57  fof(f391,plain,(
% 0.19/0.57    m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(subsumption_resolution,[],[f390,f48])).
% 0.19/0.57  fof(f390,plain,(
% 0.19/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(subsumption_resolution,[],[f389,f47])).
% 0.19/0.57  fof(f389,plain,(
% 0.19/0.57    ~v3_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | m1_subset_1(k2_funct_2(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.57    inference(resolution,[],[f380,f46])).
% 0.19/0.57  fof(f380,plain,(
% 0.19/0.57    ( ! [X0] : (~v1_funct_2(sK2,X0,X0) | ~v3_funct_2(sK2,X0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.57    inference(resolution,[],[f65,f45])).
% 0.19/0.57  fof(f65,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f31])).
% 0.19/0.57  fof(f31,plain,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.19/0.57    inference(flattening,[],[f30])).
% 0.19/0.57  fof(f30,plain,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f15])).
% 0.19/0.57  fof(f15,axiom,(
% 0.19/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.19/0.57  fof(f941,plain,(
% 0.19/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 0.19/0.57    inference(backward_demodulation,[],[f773,f878])).
% 0.19/0.57  fof(f878,plain,(
% 0.19/0.57    k1_xboole_0 = sK1),
% 0.19/0.57    inference(resolution,[],[f656,f255])).
% 0.19/0.57  fof(f656,plain,(
% 0.19/0.57    r1_tarski(sK1,k1_xboole_0)),
% 0.19/0.57    inference(forward_demodulation,[],[f572,f86])).
% 0.19/0.57  fof(f572,plain,(
% 0.19/0.57    r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 0.19/0.57    inference(backward_demodulation,[],[f94,f563])).
% 0.19/0.57  fof(f94,plain,(
% 0.19/0.57    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.19/0.57    inference(resolution,[],[f70,f54])).
% 0.19/0.57  fof(f773,plain,(
% 0.19/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1))),
% 0.19/0.57    inference(backward_demodulation,[],[f593,f736])).
% 0.19/0.57  fof(f593,plain,(
% 0.19/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 0.19/0.57    inference(backward_demodulation,[],[f278,f563])).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (32580)------------------------------
% 0.19/0.57  % (32580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (32580)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (32580)Memory used [KB]: 6780
% 0.19/0.57  % (32580)Time elapsed: 0.149 s
% 0.19/0.57  % (32580)------------------------------
% 0.19/0.57  % (32580)------------------------------
% 0.19/0.57  % (32571)Success in time 0.219 s
%------------------------------------------------------------------------------
