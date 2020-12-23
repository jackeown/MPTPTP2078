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
% DateTime   : Thu Dec  3 13:00:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 367 expanded)
%              Number of leaves         :   24 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  449 (1749 expanded)
%              Number of equality atoms :  137 ( 543 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f190,f239,f242,f265,f287,f307])).

fof(f307,plain,
    ( ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f306])).

% (18523)Refutation not found, incomplete strategy% (18523)------------------------------
% (18523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f306,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f305,f80])).

fof(f80,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f305,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f264,f207])).

fof(f207,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f264,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_12
  <=> sP0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f287,plain,
    ( spl8_3
    | ~ spl8_4
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f275,f51])).

fof(f51,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f275,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_3
    | ~ spl8_4
    | spl8_8 ),
    inference(backward_demodulation,[],[f154,f269])).

fof(f269,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f268,f208])).

fof(f208,plain,
    ( k1_xboole_0 != sK3
    | spl8_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f268,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f267,f243])).

fof(f243,plain,
    ( v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f45,f149])).

fof(f149,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f45,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK4 != k2_relset_1(sK3,sK4,sK5)
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK4 != k2_relset_1(sK3,sK4,sK5)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK5,X4) = X3
          & r2_hidden(X4,sK3) )
     => ( k1_funct_1(sK5,sK6(X3)) = X3
        & r2_hidden(sK6(X3),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f267,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl8_4 ),
    inference(resolution,[],[f250,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f250,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f118,f149])).

fof(f118,plain,(
    sP2(sK5,sK4,sK3) ),
    inference(resolution,[],[f74,f46])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f28,f27,f26])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f154,plain,
    ( k1_xboole_0 != k2_relat_1(sK5)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f153,f82])).

fof(f82,plain,(
    v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f81,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,
    ( v1_relat_1(sK5)
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f54,f46])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f153,plain,
    ( k1_xboole_0 != k2_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(superposition,[],[f146,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f146,plain,
    ( k1_xboole_0 != k1_relat_1(sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_3
  <=> k1_xboole_0 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

% (18522)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f265,plain,
    ( spl8_5
    | spl8_12
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f260,f148,f262,f183])).

fof(f183,plain,
    ( spl8_5
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f260,plain,
    ( sP0(sK3,k1_xboole_0)
    | sK3 = k1_relat_1(sK5)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f254,f243])).

fof(f254,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | sP0(sK3,k1_xboole_0)
    | sK3 = k1_relat_1(sK5)
    | ~ spl8_4 ),
    inference(resolution,[],[f244,f174])).

fof(f174,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f69,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f244,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f46,f149])).

fof(f242,plain,
    ( spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f241,f187,f148])).

fof(f187,plain,
    ( spl8_6
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f241,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_6 ),
    inference(resolution,[],[f189,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f189,plain,
    ( sP0(sK3,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f187])).

fof(f239,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f237,f82])).

fof(f237,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f236,f100])).

fof(f100,plain,(
    v5_relat_1(sK5,sK4) ),
    inference(resolution,[],[f66,f46])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f236,plain,
    ( ~ v5_relat_1(sK5,sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f233,f140])).

fof(f140,plain,(
    sK4 != k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f139,f46])).

fof(f139,plain,
    ( sK4 != k2_relat_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(superposition,[],[f49,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f49,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f233,plain,
    ( sK4 = k2_relat_1(sK5)
    | ~ v5_relat_1(sK5,sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(resolution,[],[f232,f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f232,plain,
    ( r1_tarski(sK4,k2_relat_1(sK5))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f231,f82])).

fof(f231,plain,
    ( r1_tarski(sK4,k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f230,f44])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f230,plain,
    ( r1_tarski(sK4,k2_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( r1_tarski(sK4,k2_relat_1(sK5))
    | r1_tarski(sK4,k2_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(resolution,[],[f228,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( ! [X3] :
            ( k1_funct_1(X1,X3) != sK7(X0,X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & r2_hidden(sK7(X0,X1),X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( k1_funct_1(X1,X3) != sK7(X0,X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X1,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & r2_hidden(X2,X0) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,sK5),sK4)
        | r1_tarski(X0,k2_relat_1(sK5)) )
    | ~ spl8_5 ),
    inference(equality_resolution,[],[f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( sK7(X1,sK5) != X0
        | r1_tarski(X1,k2_relat_1(sK5))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f226,f47])).

fof(f47,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(X0),sK3)
        | sK7(X1,sK5) != X0
        | r1_tarski(X1,k2_relat_1(sK5))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f193,f185])).

fof(f185,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f183])).

fof(f193,plain,(
    ! [X0,X1] :
      ( sK7(X1,sK5) != X0
      | r1_tarski(X1,k2_relat_1(sK5))
      | ~ r2_hidden(sK6(X0),k1_relat_1(sK5))
      | ~ r2_hidden(X0,sK4) ) ),
    inference(subsumption_resolution,[],[f192,f82])).

fof(f192,plain,(
    ! [X0,X1] :
      ( sK7(X1,sK5) != X0
      | r1_tarski(X1,k2_relat_1(sK5))
      | ~ r2_hidden(sK6(X0),k1_relat_1(sK5))
      | ~ v1_relat_1(sK5)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(subsumption_resolution,[],[f191,f44])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sK7(X1,sK5) != X0
      | r1_tarski(X1,k2_relat_1(sK5))
      | ~ r2_hidden(sK6(X0),k1_relat_1(sK5))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(superposition,[],[f59,f48])).

fof(f48,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,sK6(X3)) = X3
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) != sK7(X0,X1)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f190,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f181,f187,f183])).

fof(f181,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f180,f45])).

fof(f180,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f174,f46])).

fof(f151,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f141,f82])).

fof(f141,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f140,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (18514)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (18523)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (18514)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f308,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f151,f190,f239,f242,f265,f287,f307])).
% 0.20/0.52  fof(f307,plain,(
% 0.20/0.52    ~spl8_8 | ~spl8_12),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.52  % (18523)Refutation not found, incomplete strategy% (18523)------------------------------
% 0.20/0.52  % (18523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f306,plain,(
% 0.20/0.52    $false | (~spl8_8 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f305,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f305,plain,(
% 0.20/0.52    sP0(k1_xboole_0,k1_xboole_0) | (~spl8_8 | ~spl8_12)),
% 0.20/0.52    inference(backward_demodulation,[],[f264,f207])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    k1_xboole_0 = sK3 | ~spl8_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f206])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    spl8_8 <=> k1_xboole_0 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    sP0(sK3,k1_xboole_0) | ~spl8_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f262])).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    spl8_12 <=> sP0(sK3,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.52  fof(f287,plain,(
% 0.20/0.52    spl8_3 | ~spl8_4 | spl8_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    $false | (spl8_3 | ~spl8_4 | spl8_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f275,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl8_3 | ~spl8_4 | spl8_8)),
% 0.20/0.52    inference(backward_demodulation,[],[f154,f269])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    k1_xboole_0 = sK5 | (~spl8_4 | spl8_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f268,f208])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    k1_xboole_0 != sK3 | spl8_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f206])).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl8_4),
% 0.20/0.52    inference(subsumption_resolution,[],[f267,f243])).
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    v1_funct_2(sK5,sK3,k1_xboole_0) | ~spl8_4),
% 0.20/0.52    inference(backward_demodulation,[],[f45,f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    k1_xboole_0 = sK4 | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl8_4 <=> k1_xboole_0 = sK4),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v1_funct_2(sK5,sK3,sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f31,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) => (k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl8_4),
% 0.20/0.53    inference(resolution,[],[f250,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    sP2(sK5,k1_xboole_0,sK3) | ~spl8_4),
% 0.20/0.53    inference(backward_demodulation,[],[f118,f149])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    sP2(sK5,sK4,sK3)),
% 0.20/0.53    inference(resolution,[],[f74,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(definition_folding,[],[f25,f28,f27,f26])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(sK5) | spl8_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f153,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    v1_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_relat_1(sK5) | ~v1_relat_1(k2_zfmisc_1(sK3,sK4))),
% 0.20/0.53    inference(resolution,[],[f54,f46])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(sK5) | ~v1_relat_1(sK5) | spl8_3),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f152])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(sK5) | ~v1_relat_1(sK5) | spl8_3),
% 0.20/0.53    inference(superposition,[],[f146,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(sK5) | spl8_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    spl8_3 <=> k1_xboole_0 = k1_relat_1(sK5)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.53  % (18522)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    spl8_5 | spl8_12 | ~spl8_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f260,f148,f262,f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    spl8_5 <=> sK3 = k1_relat_1(sK5)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    sP0(sK3,k1_xboole_0) | sK3 = k1_relat_1(sK5) | ~spl8_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f254,f243])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    ~v1_funct_2(sK5,sK3,k1_xboole_0) | sP0(sK3,k1_xboole_0) | sK3 = k1_relat_1(sK5) | ~spl8_4),
% 0.20/0.53    inference(resolution,[],[f244,f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f172,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.53    inference(superposition,[],[f69,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f27])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) | ~spl8_4),
% 0.20/0.53    inference(backward_demodulation,[],[f46,f149])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    spl8_4 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f241,f187,f148])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    spl8_6 <=> sP0(sK3,sK4)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    k1_xboole_0 = sK4 | ~spl8_6),
% 0.20/0.53    inference(resolution,[],[f189,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    sP0(sK3,sK4) | ~spl8_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f187])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    ~spl8_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    $false | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f237,f82])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f236,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    v5_relat_1(sK5,sK4)),
% 0.20/0.53    inference(resolution,[],[f66,f46])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    ~v5_relat_1(sK5,sK4) | ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    sK4 != k2_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f46])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    sK4 != k2_relat_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.53    inference(superposition,[],[f49,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    sK4 != k2_relset_1(sK3,sK4,sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    sK4 = k2_relat_1(sK5) | ~v5_relat_1(sK5,sK4) | ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f232,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(resolution,[],[f62,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_relat_1(sK5)) | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f231,f82])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_relat_1(sK5)) | ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f230,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    v1_funct_1(sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f229])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    r1_tarski(sK4,k2_relat_1(sK5)) | r1_tarski(sK4,k2_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f228,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | (! [X3] : (k1_funct_1(X1,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(sK7(X0,X1),X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => (! [X3] : (k1_funct_1(X1,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (! [X3] : (k1_funct_1(X1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK7(X0,sK5),sK4) | r1_tarski(X0,k2_relat_1(sK5))) ) | ~spl8_5),
% 0.20/0.53    inference(equality_resolution,[],[f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK7(X1,sK5) != X0 | r1_tarski(X1,k2_relat_1(sK5)) | ~r2_hidden(X0,sK4)) ) | ~spl8_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK6(X0),sK3) | sK7(X1,sK5) != X0 | r1_tarski(X1,k2_relat_1(sK5)) | ~r2_hidden(X0,sK4)) ) | ~spl8_5),
% 0.20/0.53    inference(forward_demodulation,[],[f193,f185])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    sK3 = k1_relat_1(sK5) | ~spl8_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f183])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK7(X1,sK5) != X0 | r1_tarski(X1,k2_relat_1(sK5)) | ~r2_hidden(sK6(X0),k1_relat_1(sK5)) | ~r2_hidden(X0,sK4)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f192,f82])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK7(X1,sK5) != X0 | r1_tarski(X1,k2_relat_1(sK5)) | ~r2_hidden(sK6(X0),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | ~r2_hidden(X0,sK4)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f191,f44])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK7(X1,sK5) != X0 | r1_tarski(X1,k2_relat_1(sK5)) | ~r2_hidden(sK6(X0),k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~r2_hidden(X0,sK4)) )),
% 0.20/0.53    inference(superposition,[],[f59,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X3] : (k1_funct_1(sK5,sK6(X3)) = X3 | ~r2_hidden(X3,sK4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) != sK7(X0,X1) | r1_tarski(X0,k2_relat_1(X1)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    spl8_5 | spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f181,f187,f183])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f180,f45])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.20/0.53    inference(resolution,[],[f174,f46])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    ~spl8_3 | ~spl8_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f142,f148,f144])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    k1_xboole_0 != sK4 | k1_xboole_0 != k1_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f141,f82])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    k1_xboole_0 != sK4 | k1_xboole_0 != k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 0.20/0.53    inference(superposition,[],[f140,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18514)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (18514)Memory used [KB]: 6268
% 0.20/0.53  % (18514)Time elapsed: 0.077 s
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18503)Success in time 0.168 s
%------------------------------------------------------------------------------
