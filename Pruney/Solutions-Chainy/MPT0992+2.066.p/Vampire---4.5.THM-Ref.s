%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 417 expanded)
%              Number of leaves         :   24 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  459 (1951 expanded)
%              Number of equality atoms :   69 ( 395 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f112,f126,f156,f169,f201,f222,f296,f335,f427,f429])).

fof(f429,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_9 ),
    inference(subsumption_resolution,[],[f411,f388])).

fof(f388,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f363,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f363,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f50,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,(
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

fof(f411,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_9 ),
    inference(backward_demodulation,[],[f372,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(resolution,[],[f386,f54])).

fof(f54,plain,(
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

fof(f386,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f52,f94])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f372,plain,
    ( ~ v1_funct_2(sK3,sK2,k1_xboole_0)
    | ~ spl4_2
    | spl4_9 ),
    inference(backward_demodulation,[],[f168,f97])).

fof(f168,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_9
  <=> v1_funct_2(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f427,plain,
    ( ~ spl4_1
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl4_1
    | spl4_8 ),
    inference(subsumption_resolution,[],[f404,f387])).

fof(f387,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f115,f94])).

fof(f115,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f404,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1
    | spl4_8 ),
    inference(backward_demodulation,[],[f164,f402])).

fof(f164,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_8
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f335,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f333,f52])).

fof(f333,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f332,f135])).

fof(f135,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2 ),
    inference(superposition,[],[f120,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,
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
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f332,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f331,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f331,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f328,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f328,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f327,f311])).

fof(f311,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f310,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f310,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f303,f51])).

fof(f303,plain,
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f327,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f324,f66])).

fof(f324,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f323,f144])).

fof(f144,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f143,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f142,f51])).

fof(f142,plain,
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

fof(f323,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f316,f98])).

fof(f316,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f311,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f296,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f294,f49])).

fof(f294,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f288,f51])).

fof(f288,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f151,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f151,plain,
    ( ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_6
  <=> ! [X0] : ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f222,plain,
    ( spl4_7
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f219,f115])).

fof(f219,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f216,f121])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f210,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f210,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f206,f204])).

fof(f204,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f203,f49])).

fof(f203,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f202,f51])).

fof(f202,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(superposition,[],[f183,f81])).

fof(f183,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_11
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f206,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | spl4_7 ),
    inference(resolution,[],[f187,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f187,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f186,f49])).

fof(f186,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_funct_1(sK3)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f176,f51])).

fof(f176,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_7 ),
    inference(superposition,[],[f155,f81])).

fof(f155,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_7
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f201,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f194,f115])).

fof(f194,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f191,f121])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_11 ),
    inference(resolution,[],[f190,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f190,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f189,f49])).

fof(f189,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f188,f51])).

fof(f188,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(superposition,[],[f184,f81])).

fof(f184,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f169,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_4 ),
    inference(avatar_split_clause,[],[f160,f105,f166,f162])).

fof(f160,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f159,f121])).

fof(f159,plain,
    ( ~ v1_funct_2(sK3,sK2,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f144,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f156,plain,
    ( spl4_6
    | ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f145,f101,f153,f150])).

fof(f145,plain,
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f126,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(resolution,[],[f111,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(avatar_split_clause,[],[f47,f109,f105,f101])).

fof(f47,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f96,f92])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (1762)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (1761)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (1771)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (1772)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (1776)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (1779)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (1766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (1763)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (1767)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (1769)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (1775)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (1770)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (1778)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (1782)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (1760)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (1780)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (1761)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f99,f112,f126,f156,f169,f201,f222,f296,f335,f427,f429])).
% 0.21/0.50  fof(f429,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2 | spl4_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    $false | (~spl4_1 | ~spl4_2 | spl4_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f411,f388])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 0.21/0.50    inference(backward_demodulation,[],[f363,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl4_1 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_2),
% 0.21/0.50    inference(backward_demodulation,[],[f50,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl4_2 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f19])).
% 0.21/0.50  fof(f19,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f372,f402])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_1),
% 0.21/0.50    inference(resolution,[],[f386,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_xboole_0) | ~spl4_1),
% 0.21/0.50    inference(backward_demodulation,[],[f52,f94])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    r1_tarski(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK2,k1_xboole_0) | (~spl4_2 | spl4_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f168,f97])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK2,sK1) | spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl4_9 <=> v1_funct_2(sK3,sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    ~spl4_1 | spl4_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f426])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    $false | (~spl4_1 | spl4_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f404,f387])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    v4_relat_1(sK3,k1_xboole_0) | ~spl4_1),
% 0.21/0.50    inference(backward_demodulation,[],[f115,f94])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    v4_relat_1(sK3,sK0)),
% 0.21/0.50    inference(resolution,[],[f51,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,k1_xboole_0) | (~spl4_1 | spl4_8)),
% 0.21/0.50    inference(backward_demodulation,[],[f164,f402])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,sK2) | spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl4_8 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl4_2 | ~spl4_3 | spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f334])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    $false | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f333,f52])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    ~r1_tarski(sK2,sK0) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(forward_demodulation,[],[f332,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f133,f51])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_2),
% 0.21/0.50    inference(superposition,[],[f120,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f119,f50])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f51,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k1_relat_1(sK3)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f51,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f330])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(superposition,[],[f328,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f311])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f310,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f303,f51])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 0.21/0.50    inference(superposition,[],[f102,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(superposition,[],[f324,f66])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f323,f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f49])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f51])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_4),
% 0.21/0.50    inference(superposition,[],[f107,f81])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl4_4 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f316,f98])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f311,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ~spl4_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    $false | ~spl4_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f49])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | ~spl4_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f288,f51])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f151,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl4_6 <=> ! [X0] : ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl4_7 | ~spl4_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    $false | (spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(resolution,[],[f219,f115])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | (spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f216,f121])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | (spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(resolution,[],[f210,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~v4_relat_1(k7_relat_1(sK3,sK2),sK2) | (spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    v1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f203,f49])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~spl4_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f202,f51])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_11),
% 0.21/0.50    inference(superposition,[],[f183,f81])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl4_11 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v4_relat_1(k7_relat_1(sK3,sK2),sK2) | spl4_7),
% 0.21/0.50    inference(resolution,[],[f187,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f49])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~v1_funct_1(sK3) | spl4_7),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f51])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_7),
% 0.21/0.50    inference(superposition,[],[f155,f81])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl4_7 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    spl4_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    $false | spl4_11),
% 0.21/0.50    inference(resolution,[],[f194,f115])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | spl4_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f121])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_11),
% 0.21/0.50    inference(resolution,[],[f190,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f49])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | spl4_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f51])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_11),
% 0.21/0.50    inference(superposition,[],[f184,f81])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ~spl4_8 | ~spl4_9 | spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f105,f166,f162])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f121])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK2,sK1) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_4),
% 0.21/0.50    inference(superposition,[],[f144,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl4_6 | ~spl4_7 | spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f101,f153,f150])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_3),
% 0.21/0.50    inference(resolution,[],[f103,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl4_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    $false | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f49])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_5),
% 0.21/0.50    inference(resolution,[],[f111,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl4_5 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f109,f105,f101])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f96,f92])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1761)------------------------------
% 0.21/0.50  % (1761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1761)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1761)Memory used [KB]: 10746
% 0.21/0.50  % (1761)Time elapsed: 0.090 s
% 0.21/0.50  % (1761)------------------------------
% 0.21/0.50  % (1761)------------------------------
% 0.21/0.50  % (1765)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (1759)Success in time 0.145 s
%------------------------------------------------------------------------------
