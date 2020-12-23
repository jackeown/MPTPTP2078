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
% DateTime   : Thu Dec  3 13:03:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 406 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  459 (1890 expanded)
%              Number of equality atoms :   69 ( 387 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f112,f125,f154,f165,f195,f219,f276,f312,f395,f397])).

fof(f397,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f381,f359])).

fof(f359,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f340,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f340,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f51,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f381,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_7 ),
    inference(backward_demodulation,[],[f347,f372])).

fof(f372,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(resolution,[],[f357,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f357,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f53,f94])).

fof(f53,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f347,plain,
    ( ~ v1_funct_2(sK3,sK2,k1_xboole_0)
    | ~ spl4_2
    | spl4_7 ),
    inference(backward_demodulation,[],[f153,f97])).

fof(f153,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f395,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl4_1
    | spl4_6 ),
    inference(subsumption_resolution,[],[f374,f358])).

fof(f358,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f115,f94])).

fof(f115,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f374,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1
    | spl4_6 ),
    inference(backward_demodulation,[],[f149,f372])).

fof(f149,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_6
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f312,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f310,f53])).

fof(f310,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f309,f134])).

fof(f134,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f132,f52])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2 ),
    inference(superposition,[],[f119,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f119,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f118,f51])).

fof(f118,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f114,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f309,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f308,f120])).

fof(f120,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f117,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f308,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f305,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f305,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f304,f290])).

fof(f290,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f289,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f289,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f282,f52])).

fof(f282,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f102,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f102,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f304,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f302,f66])).

fof(f302,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f301,f143])).

fof(f143,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f107,f81])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f301,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f295,f98])).

fof(f295,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f290,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f276,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f274,f50])).

fof(f274,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f269,f52])).

fof(f269,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(resolution,[],[f160,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f160,plain,
    ( ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_8
  <=> ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f219,plain,
    ( spl4_9
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl4_9
    | ~ spl4_11 ),
    inference(resolution,[],[f216,f115])).

fof(f216,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f213,f120])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_9
    | ~ spl4_11 ),
    inference(resolution,[],[f207,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f207,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f203,f198])).

fof(f198,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f197,f50])).

fof(f197,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f196,f52])).

fof(f196,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(superposition,[],[f181,f81])).

fof(f181,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_11
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f203,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | spl4_9 ),
    inference(resolution,[],[f185,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f185,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f184,f50])).

fof(f184,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_funct_1(sK3)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f174,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_9 ),
    inference(superposition,[],[f164,f81])).

fof(f164,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_9
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f195,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f190,f120])).

fof(f190,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(resolution,[],[f188,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f188,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f187,f50])).

fof(f187,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f186,f52])).

fof(f186,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(superposition,[],[f182,f81])).

fof(f182,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f165,plain,
    ( spl4_8
    | ~ spl4_9
    | spl4_3 ),
    inference(avatar_split_clause,[],[f155,f101,f162,f159])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
        | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_3 ),
    inference(resolution,[],[f103,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f103,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f154,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_4 ),
    inference(avatar_split_clause,[],[f145,f105,f151,f147])).

fof(f145,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f144,f120])).

fof(f144,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f143,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f125,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f123,f50])).

fof(f123,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(resolution,[],[f111,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_5
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f112,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f48,f109,f105,f101])).

fof(f48,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f96,f92])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8173)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (8183)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (8192)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (8177)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (8191)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (8185)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (8182)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (8179)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8190)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (8180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (8176)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (8175)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (8181)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (8195)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (8174)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8194)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (8186)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (8193)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (8174)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f99,f112,f125,f154,f165,f195,f219,f276,f312,f395,f397])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_2 | spl4_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f396])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    $false | (~spl4_1 | ~spl4_2 | spl4_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f381,f359])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 0.21/0.51    inference(backward_demodulation,[],[f340,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl4_1 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_2),
% 0.21/0.51    inference(backward_demodulation,[],[f51,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl4_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f19])).
% 0.21/0.51  fof(f19,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_7)),
% 0.21/0.51    inference(backward_demodulation,[],[f347,f372])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_1),
% 0.21/0.51    inference(resolution,[],[f357,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_xboole_0) | ~spl4_1),
% 0.21/0.51    inference(backward_demodulation,[],[f53,f94])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    r1_tarski(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK2,k1_xboole_0) | (~spl4_2 | spl4_7)),
% 0.21/0.51    inference(backward_demodulation,[],[f153,f97])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK2,sK1) | spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl4_7 <=> v1_funct_2(sK3,sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ~spl4_1 | spl4_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    $false | (~spl4_1 | spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f374,f358])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    v4_relat_1(sK3,k1_xboole_0) | ~spl4_1),
% 0.21/0.51    inference(backward_demodulation,[],[f115,f94])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    v4_relat_1(sK3,sK0)),
% 0.21/0.51    inference(resolution,[],[f52,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    ~v4_relat_1(sK3,k1_xboole_0) | (~spl4_1 | spl4_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f149,f372])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~v4_relat_1(sK3,sK2) | spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl4_6 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    spl4_2 | ~spl4_3 | spl4_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    $false | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f310,f53])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    ~r1_tarski(sK2,sK0) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f309,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | spl4_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f132,f52])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_2),
% 0.21/0.51    inference(superposition,[],[f119,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f51])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | spl4_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f52,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k1_relat_1(sK3)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f308,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f52,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f307])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(superposition,[],[f305,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f304,f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f282,f52])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 0.21/0.51    inference(superposition,[],[f102,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(superposition,[],[f302,f66])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f301,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f50])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f52])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_4),
% 0.21/0.51    inference(superposition,[],[f107,f81])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl4_4 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f295,f98])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f290,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ~spl4_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    $false | ~spl4_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f274,f50])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | ~spl4_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f269,f52])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_8),
% 0.21/0.51    inference(resolution,[],[f160,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl4_8 <=> ! [X0] : ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl4_9 | ~spl4_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f217])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    $false | (spl4_9 | ~spl4_11)),
% 0.21/0.51    inference(resolution,[],[f216,f115])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | (spl4_9 | ~spl4_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f213,f120])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | (spl4_9 | ~spl4_11)),
% 0.21/0.51    inference(resolution,[],[f207,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ~v4_relat_1(k7_relat_1(sK3,sK2),sK2) | (spl4_9 | ~spl4_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f203,f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    v1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_11),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f50])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~spl4_11),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f52])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_11),
% 0.21/0.51    inference(superposition,[],[f181,f81])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl4_11 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v4_relat_1(k7_relat_1(sK3,sK2),sK2) | spl4_9),
% 0.21/0.51    inference(resolution,[],[f185,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f50])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~v1_funct_1(sK3) | spl4_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f174,f52])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_9),
% 0.21/0.51    inference(superposition,[],[f164,f81])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl4_9 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl4_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    $false | spl4_11),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f120])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl4_11),
% 0.21/0.51    inference(resolution,[],[f188,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_11),
% 0.21/0.51    inference(subsumption_resolution,[],[f187,f50])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_11),
% 0.21/0.51    inference(subsumption_resolution,[],[f186,f52])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_11),
% 0.21/0.51    inference(superposition,[],[f182,f81])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl4_8 | ~spl4_9 | spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f101,f162,f159])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_3),
% 0.21/0.51    inference(resolution,[],[f103,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(flattening,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~spl4_6 | ~spl4_7 | spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f145,f105,f151,f147])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f120])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_4),
% 0.21/0.51    inference(superposition,[],[f143,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    $false | spl4_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f123,f50])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | spl4_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f52])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_5),
% 0.21/0.51    inference(resolution,[],[f111,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl4_5 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f109,f105,f101])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl4_1 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f96,f92])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8174)------------------------------
% 0.21/0.51  % (8174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8174)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8174)Memory used [KB]: 10746
% 0.21/0.51  % (8174)Time elapsed: 0.106 s
% 0.21/0.51  % (8174)------------------------------
% 0.21/0.51  % (8174)------------------------------
% 0.21/0.51  % (8189)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (8169)Success in time 0.153 s
%------------------------------------------------------------------------------
