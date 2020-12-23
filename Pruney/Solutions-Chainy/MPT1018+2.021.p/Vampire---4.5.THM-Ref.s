%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 319 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  367 (1230 expanded)
%              Number of equality atoms :  104 ( 394 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f193,f204,f208,f226,f227,f229,f288,f305,f309,f343,f424])).

fof(f424,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f402,f345])).

fof(f345,plain,
    ( ! [X2] : k1_xboole_0 = X2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f344,f301])).

fof(f301,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl4_13
  <=> ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f344,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
        | k1_xboole_0 = X2 )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f188,f265])).

fof(f265,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f264,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f264,plain,
    ( sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f75,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f75,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_3
  <=> sK1 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f188,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK1,k1_xboole_0,X2)
        | k1_xboole_0 = X2 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_11
  <=> ! [X2] :
        ( ~ v1_funct_2(sK1,k1_xboole_0,X2)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f402,plain,
    ( k1_xboole_0 != sK2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(superposition,[],[f20,f345])).

fof(f20,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (8381)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (8383)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (8382)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8382)Termination reason: Refutation not found, incomplete strategy

% (8382)Memory used [KB]: 10490
% (8382)Time elapsed: 0.146 s
% (8382)------------------------------
% (8382)------------------------------
fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f343,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f341,f20])).

fof(f341,plain,
    ( sK2 = sK3
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f340,f338])).

fof(f338,plain,
    ( sK2 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f271,f194])).

fof(f194,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f17,f157])).

fof(f17,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f271,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X3)) = X3 )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f185,f265])).

fof(f185,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_10
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f340,plain,
    ( sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f339,f266])).

fof(f266,plain,
    ( k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f19,f265])).

fof(f19,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f339,plain,
    ( sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f271,f195])).

fof(f195,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f18,f157])).

fof(f18,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f309,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f308,f111,f108])).

fof(f108,plain,
    ( spl4_5
  <=> ! [X2] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( spl4_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f308,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f116,f98])).

fof(f98,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f86,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f104,f25])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ v1_funct_2(X1,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f51,f29])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f305,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f122,f59,f111,f300])).

fof(f59,plain,
    ( spl4_2
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f118,f60])).

fof(f60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f52,f94])).

fof(f94,plain,
    ( ! [X2] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(resolution,[],[f88,f60])).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f34,f45])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f288,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f286,f109])).

fof(f109,plain,
    ( ! [X2] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f286,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f285,f265])).

fof(f285,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f22,f157])).

fof(f22,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f229,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f228,f180,f155])).

fof(f180,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f215,f22])).

fof(f215,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,sK0,sK0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f23,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f172,f21])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2 ) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f227,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f213,f77,f73])).

fof(f77,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f213,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(resolution,[],[f66,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f30,f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f226,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f224,f20])).

fof(f224,plain,
    ( sK2 = sK3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f223,f221])).

fof(f221,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_9 ),
    inference(resolution,[],[f181,f17])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f223,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f222,f19])).

fof(f222,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_9 ),
    inference(resolution,[],[f181,f18])).

fof(f208,plain,
    ( spl4_4
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f206,f25])).

fof(f206,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f199,f44])).

fof(f199,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | spl4_4
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f79,f157])).

fof(f79,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f204,plain,
    ( ~ spl4_8
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl4_8
    | spl4_12 ),
    inference(subsumption_resolution,[],[f202,f192])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl4_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f202,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f197,f44])).

fof(f197,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f23,f157])).

fof(f193,plain,
    ( spl4_10
    | spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f177,f190,f187,f184])).

fof(f177,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(sK1,k1_xboole_0,X2)
      | ~ r2_hidden(X3,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3 ) ),
    inference(superposition,[],[f173,f45])).

fof(f65,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f63,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_2 ),
    inference(resolution,[],[f29,f61])).

fof(f61,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (8377)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.55  % (8394)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (8376)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (8378)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (8377)Refutation not found, incomplete strategy% (8377)------------------------------
% 0.21/0.56  % (8377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8376)Refutation not found, incomplete strategy% (8376)------------------------------
% 0.21/0.56  % (8376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8373)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (8375)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (8374)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (8378)Refutation not found, incomplete strategy% (8378)------------------------------
% 0.21/0.56  % (8378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8378)Memory used [KB]: 1663
% 0.21/0.56  % (8378)Time elapsed: 0.128 s
% 0.21/0.56  % (8378)------------------------------
% 0.21/0.56  % (8378)------------------------------
% 0.21/0.56  % (8384)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (8376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8376)Memory used [KB]: 6140
% 0.21/0.56  % (8376)Time elapsed: 0.128 s
% 0.21/0.56  % (8376)------------------------------
% 0.21/0.56  % (8376)------------------------------
% 0.21/0.56  % (8385)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.56  % (8386)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (8377)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8377)Memory used [KB]: 10618
% 0.21/0.56  % (8377)Time elapsed: 0.118 s
% 0.21/0.56  % (8377)------------------------------
% 0.21/0.56  % (8377)------------------------------
% 0.21/0.56  % (8384)Refutation not found, incomplete strategy% (8384)------------------------------
% 0.21/0.56  % (8384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8392)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (8384)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8384)Memory used [KB]: 6140
% 0.21/0.56  % (8384)Time elapsed: 0.129 s
% 0.21/0.56  % (8384)------------------------------
% 0.21/0.56  % (8384)------------------------------
% 0.21/0.56  % (8393)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.57  % (8391)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.57  % (8389)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.57  % (8390)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (8393)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f425,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f65,f193,f204,f208,f226,f227,f229,f288,f305,f309,f343,f424])).
% 0.21/0.58  fof(f424,plain,(
% 0.21/0.58    ~spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_13),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f423])).
% 0.21/0.58  fof(f423,plain,(
% 0.21/0.58    $false | (~spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_13)),
% 0.21/0.58    inference(subsumption_resolution,[],[f402,f345])).
% 0.21/0.58  fof(f345,plain,(
% 0.21/0.58    ( ! [X2] : (k1_xboole_0 = X2) ) | (~spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_13)),
% 0.21/0.58    inference(subsumption_resolution,[],[f344,f301])).
% 0.21/0.58  fof(f301,plain,(
% 0.21/0.58    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) ) | ~spl4_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f300])).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    spl4_13 <=> ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.58  fof(f344,plain,(
% 0.21/0.58    ( ! [X2] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X2) | k1_xboole_0 = X2) ) | (~spl4_3 | ~spl4_8 | ~spl4_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f188,f265])).
% 0.21/0.58  fof(f265,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | (~spl4_3 | ~spl4_8)),
% 0.21/0.58    inference(forward_demodulation,[],[f264,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.58  fof(f264,plain,(
% 0.21/0.58    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_8)),
% 0.21/0.58    inference(backward_demodulation,[],[f75,f157])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~spl4_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f155])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    spl4_8 <=> k1_xboole_0 = sK0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    sK1 = k2_zfmisc_1(sK0,sK0) | ~spl4_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    spl4_3 <=> sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    ( ! [X2] : (~v1_funct_2(sK1,k1_xboole_0,X2) | k1_xboole_0 = X2) ) | ~spl4_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f187])).
% 0.21/0.58  fof(f187,plain,(
% 0.21/0.58    spl4_11 <=> ! [X2] : (~v1_funct_2(sK1,k1_xboole_0,X2) | k1_xboole_0 = X2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.58  fof(f402,plain,(
% 0.21/0.58    k1_xboole_0 != sK2 | (~spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_13)),
% 0.21/0.58    inference(superposition,[],[f20,f345])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    sK2 != sK3),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.58    inference(flattening,[],[f10])).
% 0.21/0.58  fof(f10,plain,(
% 0.21/0.58    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  % (8381)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.58  % (8383)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.58  % (8382)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.58  % (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% 0.21/0.58  % (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (8382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (8382)Memory used [KB]: 10490
% 0.21/0.58  % (8382)Time elapsed: 0.146 s
% 0.21/0.58  % (8382)------------------------------
% 0.21/0.58  % (8382)------------------------------
% 0.21/0.59  fof(f9,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.59    inference(negated_conjecture,[],[f8])).
% 0.21/0.59  fof(f8,conjecture,(
% 0.21/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.59  fof(f343,plain,(
% 0.21/0.59    ~spl4_3 | ~spl4_8 | ~spl4_10),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.59  fof(f342,plain,(
% 0.21/0.59    $false | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(subsumption_resolution,[],[f341,f20])).
% 0.21/0.59  fof(f341,plain,(
% 0.21/0.59    sK2 = sK3 | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(forward_demodulation,[],[f340,f338])).
% 0.21/0.59  fof(f338,plain,(
% 0.21/0.59    sK2 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(resolution,[],[f271,f194])).
% 0.21/0.59  fof(f194,plain,(
% 0.21/0.59    r2_hidden(sK2,k1_xboole_0) | ~spl4_8),
% 0.21/0.59    inference(backward_demodulation,[],[f17,f157])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    r2_hidden(sK2,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f271,plain,(
% 0.21/0.59    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X3)) = X3) ) | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(backward_demodulation,[],[f185,f265])).
% 0.21/0.59  fof(f185,plain,(
% 0.21/0.59    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3) ) | ~spl4_10),
% 0.21/0.59    inference(avatar_component_clause,[],[f184])).
% 0.21/0.59  fof(f184,plain,(
% 0.21/0.59    spl4_10 <=> ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.59  fof(f340,plain,(
% 0.21/0.59    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(forward_demodulation,[],[f339,f266])).
% 0.21/0.59  fof(f266,plain,(
% 0.21/0.59    k1_funct_1(k1_xboole_0,sK2) = k1_funct_1(k1_xboole_0,sK3) | (~spl4_3 | ~spl4_8)),
% 0.21/0.59    inference(backward_demodulation,[],[f19,f265])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f339,plain,(
% 0.21/0.59    sK3 = k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3)) | (~spl4_3 | ~spl4_8 | ~spl4_10)),
% 0.21/0.59    inference(resolution,[],[f271,f195])).
% 0.21/0.59  fof(f195,plain,(
% 0.21/0.59    r2_hidden(sK3,k1_xboole_0) | ~spl4_8),
% 0.21/0.59    inference(backward_demodulation,[],[f18,f157])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    r2_hidden(sK3,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f309,plain,(
% 0.21/0.59    spl4_5 | spl4_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f308,f111,f108])).
% 0.21/0.59  fof(f108,plain,(
% 0.21/0.59    spl4_5 <=> ! [X2] : ~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    spl4_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.59  fof(f308,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f116,f98])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.59    inference(resolution,[],[f86,f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.59  fof(f86,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.59    inference(resolution,[],[f34,f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.59  fof(f116,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.59    inference(resolution,[],[f104,f25])).
% 0.21/0.59  fof(f104,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~v1_funct_2(X1,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1)) )),
% 0.21/0.59    inference(resolution,[],[f51,f29])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f46,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(flattening,[],[f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.59  fof(f305,plain,(
% 0.21/0.59    spl4_13 | ~spl4_6 | ~spl4_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f122,f59,f111,f300])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    spl4_2 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.59  fof(f122,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_2),
% 0.21/0.59    inference(subsumption_resolution,[],[f118,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f59])).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_2),
% 0.21/0.59    inference(superposition,[],[f52,f94])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    ( ! [X2] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)) ) | ~spl4_2),
% 0.21/0.59    inference(resolution,[],[f88,f60])).
% 0.21/0.59  fof(f88,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 0.21/0.59    inference(superposition,[],[f34,f45])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f47,f45])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f288,plain,(
% 0.21/0.59    ~spl4_3 | ~spl4_5 | ~spl4_8),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.59  fof(f287,plain,(
% 0.21/0.59    $false | (~spl4_3 | ~spl4_5 | ~spl4_8)),
% 0.21/0.59    inference(subsumption_resolution,[],[f286,f109])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ( ! [X2] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) ) | ~spl4_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f108])).
% 0.21/0.59  fof(f286,plain,(
% 0.21/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_8)),
% 0.21/0.59    inference(forward_demodulation,[],[f285,f265])).
% 0.21/0.59  fof(f285,plain,(
% 0.21/0.59    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl4_8),
% 0.21/0.59    inference(forward_demodulation,[],[f22,f157])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f229,plain,(
% 0.21/0.59    spl4_8 | spl4_9),
% 0.21/0.59    inference(avatar_split_clause,[],[f228,f180,f155])).
% 0.21/0.59  fof(f180,plain,(
% 0.21/0.59    spl4_9 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.59  fof(f228,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f215,f22])).
% 0.21/0.59  fof(f215,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_funct_2(sK1,sK0,sK0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.59    inference(resolution,[],[f23,f173])).
% 0.21/0.59  fof(f173,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f172,f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    v1_funct_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f172,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2) )),
% 0.21/0.59    inference(resolution,[],[f41,f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    v2_funct_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.21/0.59    inference(cnf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.59    inference(flattening,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f227,plain,(
% 0.21/0.59    spl4_3 | ~spl4_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f213,f77,f73])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.59  fof(f213,plain,(
% 0.21/0.59    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.21/0.59    inference(resolution,[],[f66,f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.21/0.59    inference(resolution,[],[f30,f23])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f226,plain,(
% 0.21/0.59    ~spl4_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.59  fof(f225,plain,(
% 0.21/0.59    $false | ~spl4_9),
% 0.21/0.59    inference(subsumption_resolution,[],[f224,f20])).
% 0.21/0.59  fof(f224,plain,(
% 0.21/0.59    sK2 = sK3 | ~spl4_9),
% 0.21/0.59    inference(forward_demodulation,[],[f223,f221])).
% 0.21/0.59  fof(f221,plain,(
% 0.21/0.59    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f181,f17])).
% 0.21/0.59  fof(f181,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl4_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f180])).
% 0.21/0.59  fof(f223,plain,(
% 0.21/0.59    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_9),
% 0.21/0.59    inference(forward_demodulation,[],[f222,f19])).
% 0.21/0.59  fof(f222,plain,(
% 0.21/0.59    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~spl4_9),
% 0.21/0.59    inference(resolution,[],[f181,f18])).
% 0.21/0.59  fof(f208,plain,(
% 0.21/0.59    spl4_4 | ~spl4_8),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.59  fof(f207,plain,(
% 0.21/0.59    $false | (spl4_4 | ~spl4_8)),
% 0.21/0.59    inference(subsumption_resolution,[],[f206,f25])).
% 0.21/0.59  fof(f206,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,sK1) | (spl4_4 | ~spl4_8)),
% 0.21/0.59    inference(forward_demodulation,[],[f199,f44])).
% 0.21/0.59  fof(f199,plain,(
% 0.21/0.59    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | (spl4_4 | ~spl4_8)),
% 0.21/0.59    inference(backward_demodulation,[],[f79,f157])).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | spl4_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f77])).
% 0.21/0.59  fof(f204,plain,(
% 0.21/0.59    ~spl4_8 | spl4_12),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.59  fof(f203,plain,(
% 0.21/0.59    $false | (~spl4_8 | spl4_12)),
% 0.21/0.59    inference(subsumption_resolution,[],[f202,f192])).
% 0.21/0.59  fof(f192,plain,(
% 0.21/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl4_12),
% 0.21/0.59    inference(avatar_component_clause,[],[f190])).
% 0.21/0.59  fof(f190,plain,(
% 0.21/0.59    spl4_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.59  fof(f202,plain,(
% 0.21/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.59    inference(forward_demodulation,[],[f197,f44])).
% 0.21/0.59  fof(f197,plain,(
% 0.21/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_8),
% 0.21/0.59    inference(backward_demodulation,[],[f23,f157])).
% 0.21/0.59  fof(f193,plain,(
% 0.21/0.59    spl4_10 | spl4_11 | ~spl4_12),
% 0.21/0.59    inference(avatar_split_clause,[],[f177,f190,f187,f184])).
% 0.21/0.59  fof(f177,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK1,k1_xboole_0,X2) | ~r2_hidden(X3,k1_xboole_0) | k1_xboole_0 = X2 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X3)) = X3) )),
% 0.21/0.59    inference(superposition,[],[f173,f45])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    spl4_2),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    $false | spl4_2),
% 0.21/0.59    inference(subsumption_resolution,[],[f63,f25])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_2),
% 0.21/0.59    inference(resolution,[],[f29,f61])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f59])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (8393)------------------------------
% 0.21/0.59  % (8393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (8393)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (8393)Memory used [KB]: 10746
% 0.21/0.59  % (8393)Time elapsed: 0.140 s
% 0.21/0.59  % (8393)------------------------------
% 0.21/0.59  % (8393)------------------------------
% 0.21/0.59  % (8370)Success in time 0.226 s
%------------------------------------------------------------------------------
