%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:19 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 472 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  528 (2160 expanded)
%              Number of equality atoms :   69 ( 427 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f146,f164,f220,f280,f307,f314,f384,f425,f527,f529])).

fof(f529,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f509,f485])).

fof(f485,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f453,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f453,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f72,f131])).

fof(f131,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f509,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(backward_demodulation,[],[f462,f500])).

fof(f500,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(resolution,[],[f483,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f483,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f74,f128])).

fof(f74,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f462,plain,
    ( ~ v1_funct_2(sK3,sK2,k1_xboole_0)
    | ~ spl4_2
    | spl4_7 ),
    inference(backward_demodulation,[],[f219,f131])).

fof(f219,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f527,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl4_1
    | spl4_6 ),
    inference(subsumption_resolution,[],[f502,f484])).

fof(f484,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f149,f128])).

fof(f149,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f73,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f502,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1
    | spl4_6 ),
    inference(backward_demodulation,[],[f215,f500])).

fof(f215,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_6
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f425,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f423,f74])).

fof(f423,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f422,f173])).

fof(f173,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f171,f73])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2 ),
    inference(superposition,[],[f155,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f154,f72])).

fof(f154,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f148,f132])).

fof(f132,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f73,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f422,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f421,f156])).

fof(f156,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f421,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f420])).

fof(f420,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f418,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f418,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f417,f400])).

fof(f400,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f399,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f399,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f396,f73])).

fof(f396,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f136,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f136,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f417,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f414,f101])).

fof(f414,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f413,f207])).

fof(f207,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f206,f71])).

fof(f206,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f205,f73])).

fof(f205,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f141,f117])).

fof(f141,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_4
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f413,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f405,f132])).

fof(f405,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f400,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f384,plain,
    ( ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f382,f150])).

fof(f150,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f73,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f382,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f380,f156])).

fof(f380,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK1)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f378,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f378,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f374,f156])).

fof(f374,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f350,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f344,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f344,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f343,f283])).

fof(f283,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f282,f71])).

fof(f282,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f281,f73])).

fof(f281,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(superposition,[],[f262,f117])).

fof(f262,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl4_11
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f343,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f337,f169])).

fof(f169,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f168,f71])).

fof(f168,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f167,f73])).

fof(f167,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f144,f117])).

fof(f144,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_5
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f337,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_12 ),
    inference(resolution,[],[f302,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f302,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_12
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f314,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f308,f156])).

fof(f308,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_13 ),
    inference(resolution,[],[f306,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f306,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_13
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f307,plain,
    ( spl4_12
    | ~ spl4_13
    | spl4_3 ),
    inference(avatar_split_clause,[],[f285,f135,f304,f301])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_3 ),
    inference(resolution,[],[f238,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f238,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f237,f71])).

fof(f237,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f228,f73])).

fof(f228,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(superposition,[],[f137,f117])).

fof(f137,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f280,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f272,f156])).

fof(f272,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(resolution,[],[f269,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f269,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f268,f71])).

fof(f268,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f267,f73])).

fof(f267,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(superposition,[],[f263,f117])).

fof(f263,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f261])).

fof(f220,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_4 ),
    inference(avatar_split_clause,[],[f211,f139,f217,f213])).

fof(f211,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f210,f156])).

fof(f210,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f207,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f164,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f162,f156])).

fof(f162,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f160,f71])).

fof(f160,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(resolution,[],[f159,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f159,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_5 ),
    inference(subsumption_resolution,[],[f158,f71])).

fof(f158,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f157,f73])).

fof(f157,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(superposition,[],[f145,f117])).

fof(f145,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f146,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f69,f143,f139,f135])).

fof(f69,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f133,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f70,f130,f126])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (30110)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (30104)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (30097)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (30107)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (30099)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (30102)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (30111)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (30112)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (30103)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.55  % (30113)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.55  % (30109)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.56  % (30115)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.61/0.56  % (30106)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.61/0.56  % (30095)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.61/0.57  % (30098)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.77/0.59  % (30114)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.77/0.60  % (30101)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.77/0.60  % (30096)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.61  % (30100)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.77/0.62  % (30108)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.23/0.64  % (30116)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 2.23/0.65  % (30096)Refutation found. Thanks to Tanya!
% 2.23/0.65  % SZS status Theorem for theBenchmark
% 2.23/0.65  % SZS output start Proof for theBenchmark
% 2.23/0.65  fof(f532,plain,(
% 2.23/0.65    $false),
% 2.23/0.65    inference(avatar_sat_refutation,[],[f133,f146,f164,f220,f280,f307,f314,f384,f425,f527,f529])).
% 2.23/0.65  fof(f529,plain,(
% 2.23/0.65    ~spl4_1 | ~spl4_2 | spl4_7),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f528])).
% 2.23/0.65  fof(f528,plain,(
% 2.23/0.65    $false | (~spl4_1 | ~spl4_2 | spl4_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f509,f485])).
% 2.23/0.65  fof(f485,plain,(
% 2.23/0.65    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 2.23/0.65    inference(backward_demodulation,[],[f453,f128])).
% 2.23/0.65  fof(f128,plain,(
% 2.23/0.65    k1_xboole_0 = sK0 | ~spl4_1),
% 2.23/0.65    inference(avatar_component_clause,[],[f126])).
% 2.23/0.65  fof(f126,plain,(
% 2.23/0.65    spl4_1 <=> k1_xboole_0 = sK0),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.23/0.65  fof(f453,plain,(
% 2.23/0.65    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_2),
% 2.23/0.65    inference(backward_demodulation,[],[f72,f131])).
% 2.23/0.65  fof(f131,plain,(
% 2.23/0.65    k1_xboole_0 = sK1 | ~spl4_2),
% 2.23/0.65    inference(avatar_component_clause,[],[f130])).
% 2.23/0.65  fof(f130,plain,(
% 2.23/0.65    spl4_2 <=> k1_xboole_0 = sK1),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.23/0.65  fof(f72,plain,(
% 2.23/0.65    v1_funct_2(sK3,sK0,sK1)),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  fof(f32,plain,(
% 2.23/0.65    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.23/0.65    inference(flattening,[],[f31])).
% 2.23/0.65  fof(f31,plain,(
% 2.23/0.65    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.23/0.65    inference(ennf_transformation,[],[f30])).
% 2.23/0.65  fof(f30,negated_conjecture,(
% 2.23/0.65    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.23/0.65    inference(negated_conjecture,[],[f29])).
% 2.23/0.65  fof(f29,conjecture,(
% 2.23/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 2.23/0.65  fof(f509,plain,(
% 2.23/0.65    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_7)),
% 2.23/0.65    inference(backward_demodulation,[],[f462,f500])).
% 2.23/0.65  fof(f500,plain,(
% 2.23/0.65    k1_xboole_0 = sK2 | ~spl4_1),
% 2.23/0.65    inference(resolution,[],[f483,f78])).
% 2.23/0.65  fof(f78,plain,(
% 2.23/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.23/0.65    inference(cnf_transformation,[],[f35])).
% 2.23/0.65  fof(f35,plain,(
% 2.23/0.65    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.23/0.65    inference(ennf_transformation,[],[f2])).
% 2.23/0.65  fof(f2,axiom,(
% 2.23/0.65    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.23/0.65  fof(f483,plain,(
% 2.23/0.65    r1_tarski(sK2,k1_xboole_0) | ~spl4_1),
% 2.23/0.65    inference(backward_demodulation,[],[f74,f128])).
% 2.23/0.65  fof(f74,plain,(
% 2.23/0.65    r1_tarski(sK2,sK0)),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  fof(f462,plain,(
% 2.23/0.65    ~v1_funct_2(sK3,sK2,k1_xboole_0) | (~spl4_2 | spl4_7)),
% 2.23/0.65    inference(backward_demodulation,[],[f219,f131])).
% 2.23/0.65  fof(f219,plain,(
% 2.23/0.65    ~v1_funct_2(sK3,sK2,sK1) | spl4_7),
% 2.23/0.65    inference(avatar_component_clause,[],[f217])).
% 2.23/0.65  fof(f217,plain,(
% 2.23/0.65    spl4_7 <=> v1_funct_2(sK3,sK2,sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.23/0.65  fof(f527,plain,(
% 2.23/0.65    ~spl4_1 | spl4_6),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f526])).
% 2.23/0.65  fof(f526,plain,(
% 2.23/0.65    $false | (~spl4_1 | spl4_6)),
% 2.23/0.65    inference(subsumption_resolution,[],[f502,f484])).
% 2.23/0.65  fof(f484,plain,(
% 2.23/0.65    v4_relat_1(sK3,k1_xboole_0) | ~spl4_1),
% 2.23/0.65    inference(backward_demodulation,[],[f149,f128])).
% 2.23/0.65  fof(f149,plain,(
% 2.23/0.65    v4_relat_1(sK3,sK0)),
% 2.23/0.65    inference(resolution,[],[f73,f102])).
% 2.23/0.65  fof(f102,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f54])).
% 2.23/0.65  fof(f54,plain,(
% 2.23/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.65    inference(ennf_transformation,[],[f22])).
% 2.23/0.65  fof(f22,axiom,(
% 2.23/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.23/0.65  fof(f73,plain,(
% 2.23/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  fof(f502,plain,(
% 2.23/0.65    ~v4_relat_1(sK3,k1_xboole_0) | (~spl4_1 | spl4_6)),
% 2.23/0.65    inference(backward_demodulation,[],[f215,f500])).
% 2.23/0.65  fof(f215,plain,(
% 2.23/0.65    ~v4_relat_1(sK3,sK2) | spl4_6),
% 2.23/0.65    inference(avatar_component_clause,[],[f213])).
% 2.23/0.65  fof(f213,plain,(
% 2.23/0.65    spl4_6 <=> v4_relat_1(sK3,sK2)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.23/0.65  fof(f425,plain,(
% 2.23/0.65    spl4_2 | ~spl4_3 | spl4_4),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f424])).
% 2.23/0.65  fof(f424,plain,(
% 2.23/0.65    $false | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(subsumption_resolution,[],[f423,f74])).
% 2.23/0.65  fof(f423,plain,(
% 2.23/0.65    ~r1_tarski(sK2,sK0) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(forward_demodulation,[],[f422,f173])).
% 2.23/0.65  fof(f173,plain,(
% 2.23/0.65    sK0 = k1_relat_1(sK3) | spl4_2),
% 2.23/0.65    inference(subsumption_resolution,[],[f171,f73])).
% 2.23/0.65  fof(f171,plain,(
% 2.23/0.65    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_2),
% 2.23/0.65    inference(superposition,[],[f155,f101])).
% 2.23/0.65  fof(f101,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f53])).
% 2.23/0.65  fof(f53,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.65    inference(ennf_transformation,[],[f23])).
% 2.23/0.65  fof(f23,axiom,(
% 2.23/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.23/0.65  fof(f155,plain,(
% 2.23/0.65    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_2),
% 2.23/0.65    inference(subsumption_resolution,[],[f154,f72])).
% 2.23/0.65  fof(f154,plain,(
% 2.23/0.65    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | spl4_2),
% 2.23/0.65    inference(subsumption_resolution,[],[f148,f132])).
% 2.23/0.65  fof(f132,plain,(
% 2.23/0.65    k1_xboole_0 != sK1 | spl4_2),
% 2.23/0.65    inference(avatar_component_clause,[],[f130])).
% 2.23/0.65  fof(f148,plain,(
% 2.23/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 2.23/0.65    inference(resolution,[],[f73,f109])).
% 2.23/0.65  fof(f109,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f56])).
% 2.23/0.65  fof(f56,plain,(
% 2.23/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.65    inference(flattening,[],[f55])).
% 2.23/0.65  fof(f55,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.65    inference(ennf_transformation,[],[f26])).
% 2.23/0.65  fof(f26,axiom,(
% 2.23/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.23/0.65  fof(f422,plain,(
% 2.23/0.65    ~r1_tarski(sK2,k1_relat_1(sK3)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(subsumption_resolution,[],[f421,f156])).
% 2.23/0.65  fof(f156,plain,(
% 2.23/0.65    v1_relat_1(sK3)),
% 2.23/0.65    inference(subsumption_resolution,[],[f153,f79])).
% 2.23/0.65  fof(f79,plain,(
% 2.23/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f12])).
% 2.23/0.65  fof(f12,axiom,(
% 2.23/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.23/0.65  fof(f153,plain,(
% 2.23/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 2.23/0.65    inference(resolution,[],[f73,f77])).
% 2.23/0.65  fof(f77,plain,(
% 2.23/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f34])).
% 2.23/0.65  fof(f34,plain,(
% 2.23/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f7])).
% 2.23/0.65  fof(f7,axiom,(
% 2.23/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.23/0.65  fof(f421,plain,(
% 2.23/0.65    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(trivial_inequality_removal,[],[f420])).
% 2.23/0.65  fof(f420,plain,(
% 2.23/0.65    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(superposition,[],[f418,f85])).
% 2.23/0.65  fof(f85,plain,(
% 2.23/0.65    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f42])).
% 2.23/0.65  fof(f42,plain,(
% 2.23/0.65    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(flattening,[],[f41])).
% 2.23/0.65  fof(f41,plain,(
% 2.23/0.65    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f18])).
% 2.23/0.65  fof(f18,axiom,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.23/0.65  fof(f418,plain,(
% 2.23/0.65    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(subsumption_resolution,[],[f417,f400])).
% 2.23/0.65  fof(f400,plain,(
% 2.23/0.65    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 2.23/0.65    inference(subsumption_resolution,[],[f399,f71])).
% 2.23/0.65  fof(f71,plain,(
% 2.23/0.65    v1_funct_1(sK3)),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  fof(f399,plain,(
% 2.23/0.65    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.23/0.65    inference(subsumption_resolution,[],[f396,f73])).
% 2.23/0.65  fof(f396,plain,(
% 2.23/0.65    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 2.23/0.65    inference(superposition,[],[f136,f117])).
% 2.23/0.65  fof(f117,plain,(
% 2.23/0.65    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f68])).
% 2.23/0.65  fof(f68,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.23/0.65    inference(flattening,[],[f67])).
% 2.23/0.65  fof(f67,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.23/0.65    inference(ennf_transformation,[],[f27])).
% 2.23/0.65  fof(f27,axiom,(
% 2.23/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.23/0.65  fof(f136,plain,(
% 2.23/0.65    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 2.23/0.65    inference(avatar_component_clause,[],[f135])).
% 2.23/0.65  fof(f135,plain,(
% 2.23/0.65    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.23/0.65  fof(f417,plain,(
% 2.23/0.65    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(superposition,[],[f414,f101])).
% 2.23/0.65  fof(f414,plain,(
% 2.23/0.65    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 2.23/0.65    inference(subsumption_resolution,[],[f413,f207])).
% 2.23/0.65  fof(f207,plain,(
% 2.23/0.65    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 2.23/0.65    inference(subsumption_resolution,[],[f206,f71])).
% 2.23/0.65  fof(f206,plain,(
% 2.23/0.65    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_4),
% 2.23/0.65    inference(subsumption_resolution,[],[f205,f73])).
% 2.23/0.65  fof(f205,plain,(
% 2.23/0.65    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_4),
% 2.23/0.65    inference(superposition,[],[f141,f117])).
% 2.23/0.65  fof(f141,plain,(
% 2.23/0.65    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_4),
% 2.23/0.65    inference(avatar_component_clause,[],[f139])).
% 2.23/0.65  fof(f139,plain,(
% 2.23/0.65    spl4_4 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.23/0.65  fof(f413,plain,(
% 2.23/0.65    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_3)),
% 2.23/0.65    inference(subsumption_resolution,[],[f405,f132])).
% 2.23/0.65  fof(f405,plain,(
% 2.23/0.65    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_3),
% 2.23/0.65    inference(resolution,[],[f400,f108])).
% 2.23/0.65  fof(f108,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f56])).
% 2.23/0.65  fof(f384,plain,(
% 2.23/0.65    ~spl4_5 | ~spl4_11 | ~spl4_12),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f383])).
% 2.23/0.65  fof(f383,plain,(
% 2.23/0.65    $false | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(subsumption_resolution,[],[f382,f150])).
% 2.23/0.65  fof(f150,plain,(
% 2.23/0.65    v5_relat_1(sK3,sK1)),
% 2.23/0.65    inference(resolution,[],[f73,f103])).
% 2.23/0.65  fof(f103,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f54])).
% 2.23/0.65  fof(f382,plain,(
% 2.23/0.65    ~v5_relat_1(sK3,sK1) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(subsumption_resolution,[],[f380,f156])).
% 2.23/0.65  fof(f380,plain,(
% 2.23/0.65    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK1) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(resolution,[],[f378,f87])).
% 2.23/0.65  fof(f87,plain,(
% 2.23/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f43])).
% 2.23/0.65  fof(f43,plain,(
% 2.23/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f9])).
% 2.23/0.65  fof(f9,axiom,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.23/0.65  fof(f378,plain,(
% 2.23/0.65    ~r1_tarski(k2_relat_1(sK3),sK1) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(subsumption_resolution,[],[f374,f156])).
% 2.23/0.65  fof(f374,plain,(
% 2.23/0.65    ~r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(resolution,[],[f350,f83])).
% 2.23/0.65  fof(f83,plain,(
% 2.23/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f39])).
% 2.23/0.65  fof(f39,plain,(
% 2.23/0.65    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f20])).
% 2.23/0.65  fof(f20,axiom,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 2.23/0.65  fof(f350,plain,(
% 2.23/0.65    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~r1_tarski(X0,sK1)) ) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(resolution,[],[f344,f114])).
% 2.23/0.65  fof(f114,plain,(
% 2.23/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f62])).
% 2.23/0.65  fof(f62,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.23/0.65    inference(flattening,[],[f61])).
% 2.23/0.65  fof(f61,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.23/0.65    inference(ennf_transformation,[],[f1])).
% 2.23/0.65  fof(f1,axiom,(
% 2.23/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.23/0.65  fof(f344,plain,(
% 2.23/0.65    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (~spl4_5 | ~spl4_11 | ~spl4_12)),
% 2.23/0.65    inference(subsumption_resolution,[],[f343,f283])).
% 2.23/0.65  fof(f283,plain,(
% 2.23/0.65    v1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_11),
% 2.23/0.65    inference(subsumption_resolution,[],[f282,f71])).
% 2.23/0.65  fof(f282,plain,(
% 2.23/0.65    v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~spl4_11),
% 2.23/0.65    inference(subsumption_resolution,[],[f281,f73])).
% 2.23/0.65  fof(f281,plain,(
% 2.23/0.65    v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_11),
% 2.23/0.65    inference(superposition,[],[f262,f117])).
% 2.23/0.65  fof(f262,plain,(
% 2.23/0.65    v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_11),
% 2.23/0.65    inference(avatar_component_clause,[],[f261])).
% 2.23/0.65  fof(f261,plain,(
% 2.23/0.65    spl4_11 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.23/0.65  fof(f343,plain,(
% 2.23/0.65    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_5 | ~spl4_12)),
% 2.23/0.65    inference(subsumption_resolution,[],[f337,f169])).
% 2.23/0.65  fof(f169,plain,(
% 2.23/0.65    v1_funct_1(k7_relat_1(sK3,sK2)) | ~spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f168,f71])).
% 2.23/0.65  fof(f168,plain,(
% 2.23/0.65    v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f167,f73])).
% 2.23/0.65  fof(f167,plain,(
% 2.23/0.65    v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_5),
% 2.23/0.65    inference(superposition,[],[f144,f117])).
% 2.23/0.65  fof(f144,plain,(
% 2.23/0.65    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_5),
% 2.23/0.65    inference(avatar_component_clause,[],[f143])).
% 2.23/0.65  fof(f143,plain,(
% 2.23/0.65    spl4_5 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.23/0.65  fof(f337,plain,(
% 2.23/0.65    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_12),
% 2.23/0.65    inference(resolution,[],[f302,f93])).
% 2.23/0.65  fof(f93,plain,(
% 2.23/0.65    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f48])).
% 2.23/0.65  fof(f48,plain,(
% 2.23/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(flattening,[],[f47])).
% 2.23/0.65  fof(f47,plain,(
% 2.23/0.65    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.23/0.65    inference(ennf_transformation,[],[f28])).
% 2.23/0.65  fof(f28,axiom,(
% 2.23/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 2.23/0.65  fof(f302,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_12),
% 2.23/0.65    inference(avatar_component_clause,[],[f301])).
% 2.23/0.65  fof(f301,plain,(
% 2.23/0.65    spl4_12 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.23/0.65  fof(f314,plain,(
% 2.23/0.65    spl4_13),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f313])).
% 2.23/0.65  fof(f313,plain,(
% 2.23/0.65    $false | spl4_13),
% 2.23/0.65    inference(subsumption_resolution,[],[f308,f156])).
% 2.23/0.65  fof(f308,plain,(
% 2.23/0.65    ~v1_relat_1(sK3) | spl4_13),
% 2.23/0.65    inference(resolution,[],[f306,f82])).
% 2.23/0.65  fof(f82,plain,(
% 2.23/0.65    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f38])).
% 2.23/0.65  fof(f38,plain,(
% 2.23/0.65    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(ennf_transformation,[],[f15])).
% 2.23/0.65  fof(f15,axiom,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.23/0.65  fof(f306,plain,(
% 2.23/0.65    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_13),
% 2.23/0.65    inference(avatar_component_clause,[],[f304])).
% 2.23/0.65  fof(f304,plain,(
% 2.23/0.65    spl4_13 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.23/0.65  fof(f307,plain,(
% 2.23/0.65    spl4_12 | ~spl4_13 | spl4_3),
% 2.23/0.65    inference(avatar_split_clause,[],[f285,f135,f304,f301])).
% 2.23/0.65  fof(f285,plain,(
% 2.23/0.65    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_3),
% 2.23/0.65    inference(resolution,[],[f238,f116])).
% 2.23/0.65  fof(f116,plain,(
% 2.23/0.65    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f66])).
% 2.23/0.65  fof(f66,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.23/0.65    inference(flattening,[],[f65])).
% 2.23/0.65  fof(f65,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.23/0.65    inference(ennf_transformation,[],[f24])).
% 2.23/0.65  fof(f24,axiom,(
% 2.23/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 2.23/0.65  fof(f238,plain,(
% 2.23/0.65    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 2.23/0.65    inference(subsumption_resolution,[],[f237,f71])).
% 2.23/0.65  fof(f237,plain,(
% 2.23/0.65    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 2.23/0.65    inference(subsumption_resolution,[],[f228,f73])).
% 2.23/0.65  fof(f228,plain,(
% 2.23/0.65    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 2.23/0.65    inference(superposition,[],[f137,f117])).
% 2.23/0.65  fof(f137,plain,(
% 2.23/0.65    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 2.23/0.65    inference(avatar_component_clause,[],[f135])).
% 2.23/0.65  fof(f280,plain,(
% 2.23/0.65    spl4_11),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f279])).
% 2.23/0.65  fof(f279,plain,(
% 2.23/0.65    $false | spl4_11),
% 2.23/0.65    inference(subsumption_resolution,[],[f272,f156])).
% 2.23/0.65  fof(f272,plain,(
% 2.23/0.65    ~v1_relat_1(sK3) | spl4_11),
% 2.23/0.65    inference(resolution,[],[f269,f80])).
% 2.23/0.65  fof(f80,plain,(
% 2.23/0.65    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f36])).
% 2.23/0.65  fof(f36,plain,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f10])).
% 2.23/0.65  fof(f10,axiom,(
% 2.23/0.65    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.23/0.65  fof(f269,plain,(
% 2.23/0.65    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_11),
% 2.23/0.65    inference(subsumption_resolution,[],[f268,f71])).
% 2.23/0.65  fof(f268,plain,(
% 2.23/0.65    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_11),
% 2.23/0.65    inference(subsumption_resolution,[],[f267,f73])).
% 2.23/0.65  fof(f267,plain,(
% 2.23/0.65    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_11),
% 2.23/0.65    inference(superposition,[],[f263,f117])).
% 2.23/0.65  fof(f263,plain,(
% 2.23/0.65    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_11),
% 2.23/0.65    inference(avatar_component_clause,[],[f261])).
% 2.23/0.65  fof(f220,plain,(
% 2.23/0.65    ~spl4_6 | ~spl4_7 | spl4_4),
% 2.23/0.65    inference(avatar_split_clause,[],[f211,f139,f217,f213])).
% 2.23/0.65  fof(f211,plain,(
% 2.23/0.65    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | spl4_4),
% 2.23/0.65    inference(subsumption_resolution,[],[f210,f156])).
% 2.23/0.65  fof(f210,plain,(
% 2.23/0.65    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_4),
% 2.23/0.65    inference(superposition,[],[f207,f94])).
% 2.23/0.65  fof(f94,plain,(
% 2.23/0.65    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f50])).
% 2.23/0.65  fof(f50,plain,(
% 2.23/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.23/0.65    inference(flattening,[],[f49])).
% 2.23/0.65  fof(f49,plain,(
% 2.23/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.23/0.65    inference(ennf_transformation,[],[f14])).
% 2.23/0.65  fof(f14,axiom,(
% 2.23/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.23/0.65  fof(f164,plain,(
% 2.23/0.65    spl4_5),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f163])).
% 2.23/0.65  fof(f163,plain,(
% 2.23/0.65    $false | spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f162,f156])).
% 2.23/0.65  fof(f162,plain,(
% 2.23/0.65    ~v1_relat_1(sK3) | spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f160,f71])).
% 2.23/0.65  fof(f160,plain,(
% 2.23/0.65    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_5),
% 2.23/0.65    inference(resolution,[],[f159,f91])).
% 2.23/0.65  fof(f91,plain,(
% 2.23/0.65    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f46])).
% 2.23/0.65  fof(f46,plain,(
% 2.23/0.65    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.65    inference(flattening,[],[f45])).
% 2.23/0.65  fof(f45,plain,(
% 2.23/0.65    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f21])).
% 2.23/0.65  fof(f21,axiom,(
% 2.23/0.65    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.23/0.65  fof(f159,plain,(
% 2.23/0.65    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f158,f71])).
% 2.23/0.65  fof(f158,plain,(
% 2.23/0.65    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_5),
% 2.23/0.65    inference(subsumption_resolution,[],[f157,f73])).
% 2.23/0.65  fof(f157,plain,(
% 2.23/0.65    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_5),
% 2.23/0.65    inference(superposition,[],[f145,f117])).
% 2.23/0.65  fof(f145,plain,(
% 2.23/0.65    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_5),
% 2.23/0.65    inference(avatar_component_clause,[],[f143])).
% 2.23/0.65  fof(f146,plain,(
% 2.23/0.65    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 2.23/0.65    inference(avatar_split_clause,[],[f69,f143,f139,f135])).
% 2.23/0.65  fof(f69,plain,(
% 2.23/0.65    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  fof(f133,plain,(
% 2.23/0.65    spl4_1 | ~spl4_2),
% 2.23/0.65    inference(avatar_split_clause,[],[f70,f130,f126])).
% 2.23/0.65  fof(f70,plain,(
% 2.23/0.65    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 2.23/0.65    inference(cnf_transformation,[],[f32])).
% 2.23/0.65  % SZS output end Proof for theBenchmark
% 2.23/0.65  % (30096)------------------------------
% 2.23/0.65  % (30096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.65  % (30096)Termination reason: Refutation
% 2.23/0.65  
% 2.23/0.65  % (30096)Memory used [KB]: 10746
% 2.23/0.65  % (30096)Time elapsed: 0.197 s
% 2.23/0.65  % (30096)------------------------------
% 2.23/0.65  % (30096)------------------------------
% 2.37/0.66  % (30086)Success in time 0.301 s
%------------------------------------------------------------------------------
