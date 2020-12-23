%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 296 expanded)
%              Number of leaves         :   41 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  491 (1171 expanded)
%              Number of equality atoms :   94 ( 337 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f76,f80,f84,f88,f92,f98,f102,f110,f120,f134,f143,f158,f164,f168,f179,f183,f188,f192,f242,f249,f260,f324,f327])).

fof(f327,plain,
    ( ~ spl3_12
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f114,f323])).

fof(f323,plain,
    ( ! [X4,X5] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl3_33
  <=> ! [X5,X4] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f324,plain,
    ( spl3_31
    | spl3_33
    | ~ spl3_30
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f319,f256,f240,f322,f247])).

fof(f247,plain,
    ( spl3_31
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f240,plain,
    ( spl3_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f256,plain,
    ( spl3_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f319,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k1_xboole_0 = k1_relat_1(sK2) )
    | ~ spl3_30
    | ~ spl3_32 ),
    inference(resolution,[],[f313,f257])).

fof(f257,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f256])).

fof(f313,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = k1_relat_1(X0) )
    | ~ spl3_30 ),
    inference(resolution,[],[f286,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f286,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
        | k1_xboole_0 = k1_relat_1(X3) )
    | ~ spl3_30 ),
    inference(resolution,[],[f273,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_30 ),
    inference(resolution,[],[f272,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f272,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(X2,k1_xboole_0)
        | ~ v1_relat_1(X2)
        | k1_xboole_0 = k1_relat_1(X2) )
    | ~ spl3_30 ),
    inference(resolution,[],[f265,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f265,plain,
    ( ! [X1] :
        ( v1_xboole_0(k1_relat_1(X1))
        | ~ v4_relat_1(X1,k1_xboole_0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_30 ),
    inference(resolution,[],[f263,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_30 ),
    inference(resolution,[],[f243,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_30 ),
    inference(resolution,[],[f241,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f241,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f240])).

fof(f260,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f259,f113,f70,f67,f256])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f253,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f253,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(superposition,[],[f114,f191])).

fof(f191,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f249,plain,
    ( ~ spl3_31
    | ~ spl3_3
    | spl3_16 ),
    inference(avatar_split_clause,[],[f245,f141,f70,f247])).

fof(f141,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f245,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_3
    | spl3_16 ),
    inference(superposition,[],[f142,f71])).

fof(f142,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f242,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f223,f173,f67,f240])).

fof(f173,plain,
    ( spl3_20
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f223,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(superposition,[],[f174,f191])).

fof(f174,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f192,plain,
    ( spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f190,f173,f67])).

fof(f190,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f174,f45])).

fof(f188,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f183,plain,
    ( ~ spl3_12
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_12
    | spl3_21 ),
    inference(subsumption_resolution,[],[f114,f180])).

fof(f180,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_21 ),
    inference(resolution,[],[f178,f58])).

fof(f178,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_21
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f179,plain,
    ( ~ spl3_13
    | spl3_20
    | spl3_16
    | ~ spl3_21
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f169,f156,f113,f177,f141,f173,f118])).

fof(f118,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f156,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f169,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(resolution,[],[f157,f114])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f168,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f167,f100,f96,f74,f113])).

fof(f74,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f96,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( spl3_10
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f167,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f166,f101])).

fof(f101,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f75,f97])).

fof(f97,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f164,plain,
    ( ~ spl3_4
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_4
    | spl3_18 ),
    inference(subsumption_resolution,[],[f75,f160])).

fof(f160,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_18 ),
    inference(resolution,[],[f159,f48])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | spl3_18 ),
    inference(resolution,[],[f154,f47])).

fof(f154,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f158,plain,
    ( ~ spl3_18
    | spl3_19
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f151,f82,f156,f153])).

fof(f82,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f150,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f150,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f83])).

fof(f83,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f143,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_14 ),
    inference(avatar_split_clause,[],[f136,f132,f141,f138])).

fof(f138,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f132,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f136,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(inner_rewriting,[],[f135])).

fof(f135,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(superposition,[],[f133,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f133,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | spl3_11 ),
    inference(avatar_split_clause,[],[f129,f108,f132,f113])).

fof(f108,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_11 ),
    inference(superposition,[],[f109,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f109,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f120,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f116,f100,f96,f78,f118])).

fof(f78,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f116,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f105,f101])).

fof(f105,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f79,f97])).

fof(f79,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f110,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f106,f100,f96,f63,f108])).

fof(f63,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f103,f101])).

fof(f103,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f64,f97])).

fof(f64,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f94,f90,f100])).

fof(f90,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f94,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f44,f91])).

fof(f91,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f93,f86,f96])).

fof(f86,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f44,f87])).

fof(f87,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f88,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f42,f70,f67])).

fof(f42,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f63])).

fof(f43,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (10901)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.46  % (10901)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f329,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f65,f72,f76,f80,f84,f88,f92,f98,f102,f110,f120,f134,f143,f158,f164,f168,f179,f183,f188,f192,f242,f249,f260,f324,f327])).
% 0.22/0.46  fof(f327,plain,(
% 0.22/0.46    ~spl3_12 | ~spl3_33),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.46  fof(f325,plain,(
% 0.22/0.46    $false | (~spl3_12 | ~spl3_33)),
% 0.22/0.46    inference(subsumption_resolution,[],[f114,f323])).
% 0.22/0.46  fof(f323,plain,(
% 0.22/0.46    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl3_33),
% 0.22/0.46    inference(avatar_component_clause,[],[f322])).
% 0.22/0.46  fof(f322,plain,(
% 0.22/0.46    spl3_33 <=> ! [X5,X4] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f113])).
% 0.22/0.46  fof(f113,plain,(
% 0.22/0.46    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.46  fof(f324,plain,(
% 0.22/0.46    spl3_31 | spl3_33 | ~spl3_30 | ~spl3_32),
% 0.22/0.46    inference(avatar_split_clause,[],[f319,f256,f240,f322,f247])).
% 0.22/0.46  fof(f247,plain,(
% 0.22/0.46    spl3_31 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.46  fof(f240,plain,(
% 0.22/0.46    spl3_30 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.46  fof(f256,plain,(
% 0.22/0.46    spl3_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.46  fof(f319,plain,(
% 0.22/0.46    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_xboole_0 = k1_relat_1(sK2)) ) | (~spl3_30 | ~spl3_32)),
% 0.22/0.46    inference(resolution,[],[f313,f257])).
% 0.22/0.46  fof(f257,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_32),
% 0.22/0.46    inference(avatar_component_clause,[],[f256])).
% 0.22/0.46  fof(f313,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = k1_relat_1(X0)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f286,f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.46  fof(f286,plain,(
% 0.22/0.46    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) | ~m1_subset_1(X3,k1_zfmisc_1(X5)) | k1_xboole_0 = k1_relat_1(X3)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f273,f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.46  fof(f273,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f272,f58])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.46    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.46  fof(f272,plain,(
% 0.22/0.46    ( ! [X2] : (~v4_relat_1(X2,k1_xboole_0) | ~v1_relat_1(X2) | k1_xboole_0 = k1_relat_1(X2)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f265,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.46  fof(f265,plain,(
% 0.22/0.46    ( ! [X1] : (v1_xboole_0(k1_relat_1(X1)) | ~v4_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f263,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.46  fof(f263,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f243,f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.46    inference(nnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.46  fof(f243,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_30),
% 0.22/0.46    inference(resolution,[],[f241,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.46  fof(f241,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0) | ~spl3_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f240])).
% 0.22/0.46  fof(f260,plain,(
% 0.22/0.46    spl3_32 | ~spl3_2 | ~spl3_3 | ~spl3_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f259,f113,f70,f67,f256])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f259,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_2 | ~spl3_3 | ~spl3_12)),
% 0.22/0.46    inference(forward_demodulation,[],[f253,f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f70])).
% 0.22/0.46  fof(f253,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_2 | ~spl3_12)),
% 0.22/0.46    inference(superposition,[],[f114,f191])).
% 0.22/0.46  fof(f191,plain,(
% 0.22/0.46    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f249,plain,(
% 0.22/0.46    ~spl3_31 | ~spl3_3 | spl3_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f245,f141,f70,f247])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    spl3_16 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.46  fof(f245,plain,(
% 0.22/0.46    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_3 | spl3_16)),
% 0.22/0.46    inference(superposition,[],[f142,f71])).
% 0.22/0.46  fof(f142,plain,(
% 0.22/0.46    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_16),
% 0.22/0.46    inference(avatar_component_clause,[],[f141])).
% 0.22/0.46  fof(f242,plain,(
% 0.22/0.46    spl3_30 | ~spl3_2 | ~spl3_20),
% 0.22/0.46    inference(avatar_split_clause,[],[f223,f173,f67,f240])).
% 0.22/0.46  fof(f173,plain,(
% 0.22/0.46    spl3_20 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.46  fof(f223,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0) | (~spl3_2 | ~spl3_20)),
% 0.22/0.46    inference(superposition,[],[f174,f191])).
% 0.22/0.46  fof(f174,plain,(
% 0.22/0.46    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_20),
% 0.22/0.46    inference(avatar_component_clause,[],[f173])).
% 0.22/0.46  fof(f192,plain,(
% 0.22/0.46    spl3_2 | ~spl3_20),
% 0.22/0.46    inference(avatar_split_clause,[],[f190,f173,f67])).
% 0.22/0.46  fof(f190,plain,(
% 0.22/0.46    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_20),
% 0.22/0.46    inference(resolution,[],[f174,f45])).
% 0.22/0.46  fof(f188,plain,(
% 0.22/0.46    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.46  fof(f183,plain,(
% 0.22/0.46    ~spl3_12 | spl3_21),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.46  fof(f182,plain,(
% 0.22/0.46    $false | (~spl3_12 | spl3_21)),
% 0.22/0.46    inference(subsumption_resolution,[],[f114,f180])).
% 0.22/0.46  fof(f180,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl3_21),
% 0.22/0.46    inference(resolution,[],[f178,f58])).
% 0.22/0.46  fof(f178,plain,(
% 0.22/0.46    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_21),
% 0.22/0.46    inference(avatar_component_clause,[],[f177])).
% 0.22/0.46  fof(f177,plain,(
% 0.22/0.46    spl3_21 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.46  fof(f179,plain,(
% 0.22/0.46    ~spl3_13 | spl3_20 | spl3_16 | ~spl3_21 | ~spl3_12 | ~spl3_19),
% 0.22/0.46    inference(avatar_split_clause,[],[f169,f156,f113,f177,f141,f173,f118])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    spl3_19 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.47  fof(f169,plain,(
% 0.22/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_12 | ~spl3_19)),
% 0.22/0.47    inference(resolution,[],[f157,f114])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1)) ) | ~spl3_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f156])).
% 0.22/0.47  fof(f168,plain,(
% 0.22/0.47    spl3_12 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f167,f100,f96,f74,f113])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    spl3_10 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f167,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f166,f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f100])).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9)),
% 0.22/0.47    inference(forward_demodulation,[],[f75,f97])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f96])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f74])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    ~spl3_4 | spl3_18),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    $false | (~spl3_4 | spl3_18)),
% 0.22/0.47    inference(subsumption_resolution,[],[f75,f160])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_18),
% 0.22/0.47    inference(resolution,[],[f159,f48])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | spl3_18),
% 0.22/0.47    inference(resolution,[],[f154,f47])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | spl3_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f153])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    spl3_18 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    ~spl3_18 | spl3_19 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f151,f82,f156,f153])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_6),
% 0.22/0.47    inference(resolution,[],[f150,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.22/0.47    inference(resolution,[],[f50,f83])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f82])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.47    inference(flattening,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    ~spl3_15 | ~spl3_16 | spl3_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f136,f132,f141,f138])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    spl3_14 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_14),
% 0.22/0.47    inference(inner_rewriting,[],[f135])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_14),
% 0.22/0.47    inference(superposition,[],[f133,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f132])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ~spl3_12 | ~spl3_14 | spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f129,f108,f132,f113])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl3_11 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_11),
% 0.22/0.47    inference(superposition,[],[f109,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f108])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    spl3_13 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f116,f100,f96,f78,f118])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f105,f101])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9)),
% 0.22/0.47    inference(superposition,[],[f79,f97])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    ~spl3_11 | spl3_1 | ~spl3_9 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f106,f100,f96,f63,f108])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f103,f101])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_9)),
% 0.22/0.47    inference(superposition,[],[f64,f97])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f63])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    spl3_10 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f94,f90,f100])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl3_8 <=> l1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.22/0.47    inference(resolution,[],[f44,f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    l1_struct_0(sK0) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f90])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    spl3_9 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f93,f86,f96])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.47    inference(resolution,[],[f44,f87])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f86])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f37,f90])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    l1_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f32,f31,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f13])).
% 0.22/0.47  fof(f13,conjecture,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f38,f86])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    l1_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f82])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    v1_funct_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f40,f78])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f41,f74])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ~spl3_2 | spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f70,f67])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f63])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (10901)------------------------------
% 0.22/0.47  % (10901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (10901)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (10901)Memory used [KB]: 10874
% 0.22/0.47  % (10901)Time elapsed: 0.015 s
% 0.22/0.47  % (10901)------------------------------
% 0.22/0.47  % (10901)------------------------------
% 0.22/0.47  % (10890)Success in time 0.107 s
%------------------------------------------------------------------------------
