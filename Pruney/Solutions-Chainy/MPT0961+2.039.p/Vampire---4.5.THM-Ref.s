%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 244 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  325 ( 687 expanded)
%              Number of equality atoms :   89 ( 188 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f99,f110,f172,f252,f314,f320,f325,f332,f343,f351,f374,f383])).

fof(f383,plain,(
    spl1_15 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl1_15 ),
    inference(subsumption_resolution,[],[f381,f94])).

fof(f94,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f79,f91])).

fof(f91,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f87,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f36,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (28627)Refutation not found, incomplete strategy% (28627)------------------------------
% (28627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28627)Termination reason: Refutation not found, incomplete strategy

% (28627)Memory used [KB]: 6140
% (28627)Time elapsed: 0.092 s
% (28627)------------------------------
% (28627)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f86,f37])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f43,f79])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f79,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f381,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_15 ),
    inference(subsumption_resolution,[],[f379,f32])).

fof(f379,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_15 ),
    inference(resolution,[],[f373,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f58,f54])).

fof(f54,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f373,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_15 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl1_15
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f374,plain,
    ( ~ spl1_15
    | ~ spl1_3
    | spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f369,f348,f340,f96,f371])).

fof(f96,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f340,plain,
    ( spl1_11
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f348,plain,
    ( spl1_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f369,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | spl1_11
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f368,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f368,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_11
    | ~ spl1_12 ),
    inference(backward_demodulation,[],[f342,f350])).

fof(f350,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f348])).

fof(f342,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f340])).

fof(f351,plain,
    ( spl1_12
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f336,f311,f249,f348])).

fof(f249,plain,
    ( spl1_8
  <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f311,plain,
    ( spl1_9
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f336,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f335,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f335,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f251,f313])).

fof(f313,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f311])).

fof(f251,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f249])).

fof(f343,plain,
    ( ~ spl1_11
    | spl1_4
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f328,f311,f103,f340])).

fof(f103,plain,
    ( spl1_4
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f328,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_4
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f105,f313])).

fof(f105,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f332,plain,
    ( spl1_7
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl1_7
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f330,f70])).

fof(f330,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl1_7
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f326,f53])).

fof(f326,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0)
    | spl1_7
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f247,f313])).

fof(f247,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl1_7
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f325,plain,
    ( ~ spl1_1
    | spl1_10 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl1_1
    | spl1_10 ),
    inference(subsumption_resolution,[],[f322,f63])).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f322,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_10 ),
    inference(resolution,[],[f319,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f319,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl1_10
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f320,plain,
    ( ~ spl1_10
    | spl1_5 ),
    inference(avatar_split_clause,[],[f315,f107,f317])).

fof(f107,plain,
    ( spl1_5
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f315,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_5 ),
    inference(resolution,[],[f109,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f314,plain,
    ( ~ spl1_5
    | spl1_9
    | spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f177,f169,f103,f311,f107])).

fof(f169,plain,
    ( spl1_6
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f177,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_4
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f176,f105])).

fof(f176,plain,
    ( v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_6 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_6 ),
    inference(superposition,[],[f46,f171])).

fof(f171,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f252,plain,
    ( ~ spl1_7
    | spl1_8
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f173,f61,f249,f245])).

fof(f173,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2) ) ),
    inference(resolution,[],[f36,f33])).

fof(f172,plain,
    ( spl1_6
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f161,f61,f169])).

fof(f161,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f155,f63])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) ) ),
    inference(resolution,[],[f80,f33])).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k1_relset_1(X2,X3,X4) = k1_relat_1(X4) ) ),
    inference(resolution,[],[f42,f38])).

fof(f110,plain,
    ( ~ spl1_4
    | ~ spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f100,f66,f107,f103])).

fof(f66,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f100,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f31,f68])).

fof(f68,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f31,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f99,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f91,f96])).

fof(f69,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:09:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (28624)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (28623)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (28640)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (28623)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (28628)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (28627)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (28632)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f64,f69,f99,f110,f172,f252,f314,f320,f325,f332,f343,f351,f374,f383])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    spl1_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    $false | spl1_15),
% 0.21/0.50    inference(subsumption_resolution,[],[f381,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f79,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f87,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.50    inference(resolution,[],[f36,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f37,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  % (28627)Refutation not found, incomplete strategy% (28627)------------------------------
% 0.21/0.50  % (28627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28627)Memory used [KB]: 6140
% 0.21/0.50  % (28627)Time elapsed: 0.092 s
% 0.21/0.50  % (28627)------------------------------
% 0.21/0.50  % (28627)------------------------------
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f86,f37])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f32])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(superposition,[],[f43,f79])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f42,f32])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_15),
% 0.21/0.50    inference(subsumption_resolution,[],[f379,f32])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_15),
% 0.21/0.50    inference(resolution,[],[f373,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f58,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f371])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    spl1_15 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ~spl1_15 | ~spl1_3 | spl1_11 | ~spl1_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f369,f348,f340,f96,f371])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    spl1_11 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    spl1_12 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_3 | spl1_11 | ~spl1_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f368,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl1_11 | ~spl1_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f342,f350])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl1_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f348])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl1_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f340])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    spl1_12 | ~spl1_8 | ~spl1_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f336,f311,f249,f348])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl1_8 <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    spl1_9 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | (~spl1_8 | ~spl1_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f335,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0) | (~spl1_8 | ~spl1_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f251,f313])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f311])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ~spl1_11 | spl1_4 | ~spl1_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f328,f311,f103,f340])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl1_4 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_4 | ~spl1_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f105,f313])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    spl1_7 | ~spl1_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f331])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    $false | (spl1_7 | ~spl1_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f70])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,sK0) | (spl1_7 | ~spl1_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f326,f53])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0) | (spl1_7 | ~spl1_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f247,f313])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | spl1_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl1_7 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ~spl1_1 | spl1_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f324])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    $false | (~spl1_1 | spl1_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f322,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ~v1_relat_1(sK0) | spl1_10),
% 0.21/0.50    inference(resolution,[],[f319,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f317])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    spl1_10 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~spl1_10 | spl1_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f315,f107,f317])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl1_5 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_5),
% 0.21/0.50    inference(resolution,[],[f109,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~spl1_5 | spl1_9 | spl1_4 | ~spl1_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f177,f169,f103,f311,f107])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl1_6 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | (spl1_4 | ~spl1_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f105])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_6),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    k1_relat_1(sK0) != k1_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_6),
% 0.21/0.50    inference(superposition,[],[f46,f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f169])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ~spl1_7 | spl1_8 | ~spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f173,f61,f249,f245])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | ~spl1_1),
% 0.21/0.50    inference(resolution,[],[f74,f63])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2] : (~v1_relat_1(X2) | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2)) )),
% 0.21/0.50    inference(resolution,[],[f36,f33])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    spl1_6 | ~spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f161,f61,f169])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_1),
% 0.21/0.50    inference(resolution,[],[f155,f63])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f80,f33])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k1_relset_1(X2,X3,X4) = k1_relat_1(X4)) )),
% 0.21/0.50    inference(resolution,[],[f42,f38])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~spl1_4 | ~spl1_5 | ~spl1_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f100,f66,f107,f103])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl1_2 <=> v1_funct_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f31,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    v1_funct_1(sK0) | ~spl1_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl1_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f91,f96])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl1_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f61])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28623)------------------------------
% 0.21/0.50  % (28623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28623)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28623)Memory used [KB]: 6268
% 0.21/0.50  % (28623)Time elapsed: 0.110 s
% 0.21/0.50  % (28623)------------------------------
% 0.21/0.50  % (28623)------------------------------
% 0.21/0.50  % (28637)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (28645)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (28618)Success in time 0.149 s
%------------------------------------------------------------------------------
