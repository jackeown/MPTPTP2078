%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 257 expanded)
%              Number of leaves         :   30 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  466 ( 880 expanded)
%              Number of equality atoms :  124 ( 239 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f131,f164,f250,f277,f286,f300,f404,f415,f479,f498,f523,f602,f633])).

fof(f633,plain,
    ( ~ spl4_8
    | spl4_25
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl4_8
    | spl4_25
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f631,f377])).

fof(f377,plain,
    ( k1_xboole_0 != sK1
    | spl4_25 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f631,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_8
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f624,f163])).

fof(f163,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_8
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f624,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl4_39 ),
    inference(resolution,[],[f601,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f601,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl4_39
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f602,plain,
    ( spl4_39
    | spl4_17
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f549,f520,f495,f274,f270,f599])).

fof(f270,plain,
    ( spl4_17
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f274,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f495,plain,
    ( spl4_31
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f520,plain,
    ( spl4_32
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f549,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | spl4_17
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f536,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f536,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))
    | spl4_17
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f497,f527])).

fof(f527,plain,
    ( k1_xboole_0 = sK0
    | spl4_17
    | ~ spl4_18
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f526,f275])).

fof(f275,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f274])).

fof(f526,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_17
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f525,f272])).

fof(f272,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f270])).

fof(f525,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f524])).

fof(f524,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_32 ),
    inference(superposition,[],[f80,f522])).

fof(f522,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f520])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f497,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f495])).

fof(f523,plain,
    ( spl4_32
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f484,f274,f520])).

fof(f484,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl4_18 ),
    inference(resolution,[],[f275,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f498,plain,
    ( spl4_31
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f487,f274,f495])).

fof(f487,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl4_18 ),
    inference(resolution,[],[f275,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f479,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f104,f114,f86,f276,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f274])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_3
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f104,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f415,plain,
    ( ~ spl4_14
    | ~ spl4_19
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_19
    | spl4_27 ),
    inference(subsumption_resolution,[],[f413,f299])).

fof(f299,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_19
  <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f413,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_14
    | spl4_27 ),
    inference(subsumption_resolution,[],[f411,f243])).

fof(f243,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f411,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_27 ),
    inference(resolution,[],[f403,f301])).

fof(f301,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f97,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f403,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl4_27
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f404,plain,
    ( ~ spl4_27
    | ~ spl4_4
    | spl4_17
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f396,f376,f270,f117,f401])).

fof(f117,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f396,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f391,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f391,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK0)
    | spl4_17
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f272,f378])).

fof(f378,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f376])).

fof(f300,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f294,f266,f117,f298])).

fof(f266,plain,
    ( spl4_16
  <=> ! [X3,X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f294,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f288,f119])).

fof(f288,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_16 ),
    inference(resolution,[],[f267,f77])).

fof(f267,plain,
    ( ! [X2,X3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f266])).

fof(f286,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f285,f162,f128,f122,f117,f266])).

fof(f122,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( spl4_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f285,plain,
    ( ! [X4,X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f284,f163])).

fof(f284,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_xboole_0,X5)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f283,f119])).

fof(f283,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X5)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f282,f163])).

fof(f282,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k1_xboole_0,X4)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X5)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f279,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f279,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X4)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X5)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f130])).

fof(f130,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f277,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f264,f107,f274,f270])).

fof(f107,plain,
    ( spl4_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f264,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f50,f109])).

fof(f109,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f50,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f250,plain,
    ( ~ spl4_8
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl4_8
    | spl4_14 ),
    inference(subsumption_resolution,[],[f247,f163])).

fof(f247,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_14 ),
    inference(resolution,[],[f244,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f244,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f242])).

fof(f164,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f155,f122,f162])).

fof(f155,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f150,f124])).

fof(f150,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f90,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = sK2(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f146,f93])).

fof(f93,plain,(
    ! [X0] : v1_relat_1(sK2(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
        & k1_relat_1(sK2(X0,X1)) = X1
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f146,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2(X0,k1_xboole_0)
      | ~ v1_relat_1(sK2(X0,k1_xboole_0)) ) ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK2(X0,k1_xboole_0)
      | ~ v1_relat_1(sK2(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f54,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK2(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f90,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK2(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK2(X0,X1)),X0)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f131,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f126,f128])).

fof(f126,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f59,f88])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f122])).

fof(f52,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f120,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f115,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f49,f112])).

fof(f49,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f107])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f47,f102])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (8212)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (8212)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (8221)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (8213)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f634,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f131,f164,f250,f277,f286,f300,f404,f415,f479,f498,f523,f602,f633])).
% 0.21/0.49  fof(f633,plain,(
% 0.21/0.49    ~spl4_8 | spl4_25 | ~spl4_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f632])).
% 0.21/0.49  fof(f632,plain,(
% 0.21/0.49    $false | (~spl4_8 | spl4_25 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f631,f377])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl4_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f376])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    spl4_25 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.49  fof(f631,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | (~spl4_8 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f624,f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl4_8 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f624,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | ~spl4_39),
% 0.21/0.49    inference(resolution,[],[f601,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f601,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_xboole_0) | ~spl4_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f599])).
% 0.21/0.49  fof(f599,plain,(
% 0.21/0.49    spl4_39 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.49  fof(f602,plain,(
% 0.21/0.49    spl4_39 | spl4_17 | ~spl4_18 | ~spl4_31 | ~spl4_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f549,f520,f495,f274,f270,f599])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl4_17 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    spl4_31 <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.49  fof(f520,plain,(
% 0.21/0.49    spl4_32 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.49  fof(f549,plain,(
% 0.21/0.49    r1_tarski(sK1,k1_xboole_0) | (spl4_17 | ~spl4_18 | ~spl4_31 | ~spl4_32)),
% 0.21/0.49    inference(forward_demodulation,[],[f536,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(flattening,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f536,plain,(
% 0.21/0.49    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) | (spl4_17 | ~spl4_18 | ~spl4_31 | ~spl4_32)),
% 0.21/0.49    inference(backward_demodulation,[],[f497,f527])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | (spl4_17 | ~spl4_18 | ~spl4_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f526,f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f274])).
% 0.21/0.49  fof(f526,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (spl4_17 | ~spl4_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f525,f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl4_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f270])).
% 0.21/0.49  fof(f525,plain,(
% 0.21/0.49    v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_32),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f524])).
% 0.21/0.49  fof(f524,plain,(
% 0.21/0.49    k1_relat_1(sK1) != k1_relat_1(sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_32),
% 0.21/0.49    inference(superposition,[],[f80,f522])).
% 0.21/0.49  fof(f522,plain,(
% 0.21/0.49    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl4_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f520])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f497,plain,(
% 0.21/0.49    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~spl4_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f495])).
% 0.21/0.49  fof(f523,plain,(
% 0.21/0.49    spl4_32 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f484,f274,f520])).
% 0.21/0.49  fof(f484,plain,(
% 0.21/0.49    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl4_18),
% 0.21/0.49    inference(resolution,[],[f275,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f498,plain,(
% 0.21/0.49    spl4_31 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f487,f274,f495])).
% 0.21/0.49  fof(f487,plain,(
% 0.21/0.49    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~spl4_18),
% 0.21/0.49    inference(resolution,[],[f275,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f479,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_3 | spl4_18),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f477])).
% 0.21/0.49  fof(f477,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_3 | spl4_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f104,f114,f86,f276,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f274])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),sK0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl4_3 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl4_1 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    ~spl4_14 | ~spl4_19 | spl4_27),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f414])).
% 0.21/0.49  fof(f414,plain,(
% 0.21/0.49    $false | (~spl4_14 | ~spl4_19 | spl4_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f413,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f298])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    spl4_19 <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (~spl4_14 | spl4_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f411,f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl4_27),
% 0.21/0.49    inference(resolution,[],[f403,f301])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f97,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f403,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl4_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f401])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    spl4_27 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    ~spl4_27 | ~spl4_4 | spl4_17 | ~spl4_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f396,f376,f270,f117,f401])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl4_4 | spl4_17 | ~spl4_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f391,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK0) | (spl4_17 | ~spl4_25)),
% 0.21/0.49    inference(backward_demodulation,[],[f272,f378])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl4_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f376])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    spl4_19 | ~spl4_4 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f294,f266,f117,f298])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl4_16 <=> ! [X3,X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl4_4 | ~spl4_16)),
% 0.21/0.49    inference(forward_demodulation,[],[f288,f119])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_16),
% 0.21/0.49    inference(resolution,[],[f267,f77])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ( ! [X2,X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f266])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    spl4_16 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f285,f162,f128,f122,f117,f266])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl4_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl4_6 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    ( ! [X4,X5] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f284,f163])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r1_tarski(k1_xboole_0,X5) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f283,f119])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r1_tarski(k1_relat_1(k1_xboole_0),X5) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | (~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f163])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r1_tarski(k1_xboole_0,X4) | ~r1_tarski(k1_relat_1(k1_xboole_0),X5) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f279,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r1_tarski(k2_relat_1(k1_xboole_0),X4) | ~r1_tarski(k1_relat_1(k1_xboole_0),X5) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f76,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ~spl4_17 | ~spl4_18 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f264,f107,f274,f270])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_2 <=> v1_funct_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v1_funct_1(sK1) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~spl4_8 | spl4_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f249])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    $false | (~spl4_8 | spl4_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f247,f163])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_14),
% 0.21/0.49    inference(resolution,[],[f244,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl4_8 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f122,f162])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.21/0.49    inference(forward_demodulation,[],[f150,f124])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f90,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = sK2(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(sK2(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) & k1_relat_1(sK2(X0,X1)) = X1 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = sK2(X0,k1_xboole_0) | ~v1_relat_1(sK2(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2(X0,k1_xboole_0) | ~v1_relat_1(sK2(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(superposition,[],[f54,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(sK2(X0,k1_xboole_0)),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK2(X0,X1)),X0) | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f128])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(superposition,[],[f59,f88])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f122])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f117])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f112])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f107])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f102])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8212)------------------------------
% 0.21/0.49  % (8212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8212)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8212)Memory used [KB]: 6396
% 0.21/0.49  % (8212)Time elapsed: 0.075 s
% 0.21/0.49  % (8212)------------------------------
% 0.21/0.49  % (8212)------------------------------
% 0.21/0.49  % (8217)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (8206)Success in time 0.135 s
%------------------------------------------------------------------------------
