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
% DateTime   : Thu Dec  3 13:08:20 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 233 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 ( 920 expanded)
%              Number of equality atoms :   74 ( 152 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f98,f108,f110,f118,f135,f145,f170,f172,f188,f201,f225,f239,f241,f266,f275,f277])).

fof(f277,plain,(
    ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f33,f161])).

fof(f161,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

% (4807)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (4807)Refutation not found, incomplete strategy% (4807)------------------------------
% (4807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4807)Termination reason: Refutation not found, incomplete strategy

% (4807)Memory used [KB]: 1663
% (4807)Time elapsed: 0.002 s
% (4807)------------------------------
% (4807)------------------------------
% (4800)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (4790)Refutation not found, incomplete strategy% (4790)------------------------------
% (4790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4798)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (4790)Termination reason: Refutation not found, incomplete strategy

% (4790)Memory used [KB]: 10746
% (4790)Time elapsed: 0.136 s
% (4790)------------------------------
% (4790)------------------------------
% (4794)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (4780)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (4789)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f275,plain,
    ( ~ spl3_4
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f64,f103,f265,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( k6_partfun1(X0) != sK1
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_21
  <=> ! [X0] :
        ( k6_partfun1(X0) != sK1
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f265,plain,
    ( sK1 = k6_partfun1(sK0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_24
  <=> sK1 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f103,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_4
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f266,plain,
    ( ~ spl3_2
    | spl3_24
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f261,f191,f101,f128,f124,f263,f89])).

fof(f89,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f124,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( spl3_8
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f191,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(X0,sK1),sK0)
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f261,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_14 ),
    inference(duplicate_literal_removal,[],[f260])).

% (4784)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f260,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | ~ spl3_14 ),
    inference(resolution,[],[f192,f82])).

fof(f82,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK2(X2,X1),X2)
      | ~ v1_relat_1(X1)
      | k6_partfun1(X2) = X1
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X2)
      | ~ v1_partfun1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK2(X2,X1),X2)
      | ~ v1_relat_1(X1)
      | k6_partfun1(X2) = X1
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X2) ) ),
    inference(superposition,[],[f76,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(k1_relat_1(X0),X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k6_partfun1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f58,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f58,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(X0,sK1),sK0)
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f241,plain,
    ( ~ spl3_7
    | spl3_14
    | spl3_12 ),
    inference(avatar_split_clause,[],[f240,f181,f191,f124])).

fof(f181,plain,
    ( spl3_12
  <=> m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(X0,sK1),sK0)
        | ~ v4_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_partfun1(sK1,X0) )
    | spl3_12 ),
    inference(superposition,[],[f183,f42])).

fof(f183,plain,
    ( ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f239,plain,
    ( ~ spl3_7
    | spl3_21
    | spl3_13 ),
    inference(avatar_split_clause,[],[f235,f185,f237,f124])).

fof(f185,plain,
    ( spl3_13
  <=> sK1 = k6_partfun1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f235,plain,
    ( ! [X0] :
        ( k6_partfun1(X0) != sK1
        | ~ v4_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_partfun1(sK1,X0) )
    | spl3_13 ),
    inference(superposition,[],[f186,f42])).

fof(f186,plain,
    ( sK1 != k6_partfun1(k1_relat_1(sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f225,plain,
    ( ~ spl3_8
    | ~ spl3_4
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f219,f199,f85,f101,f128])).

fof(f85,plain,
    ( spl3_1
  <=> r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f199,plain,
    ( spl3_15
  <=> ! [X0] :
        ( k6_partfun1(X0) = sK1
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f219,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v4_relat_1(sK1,sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f32,f200])).

fof(f200,plain,
    ( ! [X0] :
        ( k6_partfun1(X0) = sK1
        | ~ v1_partfun1(sK1,X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f199])).

fof(f32,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f201,plain,
    ( ~ spl3_7
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f194,f185,f199,f124])).

fof(f194,plain,
    ( ! [X0] :
        ( k6_partfun1(X0) = sK1
        | ~ v4_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_partfun1(sK1,X0) )
    | ~ spl3_13 ),
    inference(superposition,[],[f187,f42])).

fof(f187,plain,
    ( sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f188,plain,
    ( ~ spl3_12
    | spl3_13
    | ~ spl3_7
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f179,f167,f89,f124,f185,f181])).

fof(f167,plain,
    ( spl3_11
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f179,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f57,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f57,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f172,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f31,f165])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f170,plain,
    ( spl3_9
    | ~ spl3_10
    | ~ spl3_3
    | ~ spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f156,f167,f89,f93,f163,f159])).

fof(f93,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f156,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f28,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f64,f130])).

fof(f130,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f63,f126])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

% (4793)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f118,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f34,f114])).

fof(f114,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f33,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f30,f95])).

fof(f95,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f30,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,
    ( spl3_4
    | spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f99,f93,f89,f105,f101])).

fof(f99,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0
    | v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f98,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f29,f91])).

fof(f91,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f83,f93,f89,f85])).

fof(f83,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (4779)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (4791)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (4782)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (4783)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (4782)Refutation not found, incomplete strategy% (4782)------------------------------
% 0.22/0.53  % (4782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4782)Memory used [KB]: 1791
% 0.22/0.53  % (4782)Time elapsed: 0.110 s
% 0.22/0.53  % (4782)------------------------------
% 0.22/0.53  % (4782)------------------------------
% 0.22/0.53  % (4778)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  % (4799)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.54  % (4791)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % (4779)Refutation not found, incomplete strategy% (4779)------------------------------
% 1.28/0.54  % (4779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (4779)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (4779)Memory used [KB]: 1663
% 1.28/0.54  % (4779)Time elapsed: 0.126 s
% 1.28/0.54  % (4779)------------------------------
% 1.28/0.54  % (4779)------------------------------
% 1.28/0.54  % (4790)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.54  % (4792)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f278,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(avatar_sat_refutation,[],[f96,f98,f108,f110,f118,f135,f145,f170,f172,f188,f201,f225,f239,f241,f266,f275,f277])).
% 1.28/0.54  fof(f277,plain,(
% 1.28/0.54    ~spl3_9),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f276])).
% 1.28/0.55  fof(f276,plain,(
% 1.28/0.55    $false | ~spl3_9),
% 1.28/0.55    inference(subsumption_resolution,[],[f33,f161])).
% 1.28/0.55  fof(f161,plain,(
% 1.28/0.55    v1_xboole_0(sK0) | ~spl3_9),
% 1.28/0.55    inference(avatar_component_clause,[],[f159])).
% 1.28/0.55  fof(f159,plain,(
% 1.28/0.55    spl3_9 <=> v1_xboole_0(sK0)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.28/0.55  fof(f33,plain,(
% 1.28/0.55    ~v1_xboole_0(sK0)),
% 1.28/0.55    inference(cnf_transformation,[],[f14])).
% 1.28/0.55  fof(f14,plain,(
% 1.28/0.55    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.28/0.55    inference(flattening,[],[f13])).
% 1.28/0.55  fof(f13,plain,(
% 1.28/0.55    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.28/0.55    inference(ennf_transformation,[],[f12])).
% 1.28/0.55  fof(f12,negated_conjecture,(
% 1.28/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.28/0.55    inference(negated_conjecture,[],[f11])).
% 1.28/0.55  fof(f11,conjecture,(
% 1.28/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 1.28/0.55  % (4807)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.55  % (4807)Refutation not found, incomplete strategy% (4807)------------------------------
% 1.28/0.55  % (4807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4807)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4807)Memory used [KB]: 1663
% 1.28/0.55  % (4807)Time elapsed: 0.002 s
% 1.28/0.55  % (4807)------------------------------
% 1.28/0.55  % (4807)------------------------------
% 1.28/0.55  % (4800)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.55  % (4790)Refutation not found, incomplete strategy% (4790)------------------------------
% 1.28/0.55  % (4790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4798)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.28/0.55  % (4790)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4790)Memory used [KB]: 10746
% 1.28/0.55  % (4790)Time elapsed: 0.136 s
% 1.28/0.55  % (4790)------------------------------
% 1.28/0.55  % (4790)------------------------------
% 1.28/0.55  % (4794)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.55  % (4780)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.55  % (4789)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.55  fof(f275,plain,(
% 1.28/0.55    ~spl3_4 | ~spl3_21 | ~spl3_24),
% 1.28/0.55    inference(avatar_contradiction_clause,[],[f267])).
% 1.28/0.55  fof(f267,plain,(
% 1.28/0.55    $false | (~spl3_4 | ~spl3_21 | ~spl3_24)),
% 1.28/0.55    inference(unit_resulting_resolution,[],[f64,f103,f265,f238])).
% 1.28/0.55  fof(f238,plain,(
% 1.28/0.55    ( ! [X0] : (k6_partfun1(X0) != sK1 | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0)) ) | ~spl3_21),
% 1.28/0.55    inference(avatar_component_clause,[],[f237])).
% 1.28/0.55  fof(f237,plain,(
% 1.28/0.55    spl3_21 <=> ! [X0] : (k6_partfun1(X0) != sK1 | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0))),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.28/0.55  fof(f265,plain,(
% 1.28/0.55    sK1 = k6_partfun1(sK0) | ~spl3_24),
% 1.28/0.55    inference(avatar_component_clause,[],[f263])).
% 1.28/0.55  fof(f263,plain,(
% 1.28/0.55    spl3_24 <=> sK1 = k6_partfun1(sK0)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.28/0.55  fof(f103,plain,(
% 1.28/0.55    v1_partfun1(sK1,sK0) | ~spl3_4),
% 1.28/0.55    inference(avatar_component_clause,[],[f101])).
% 1.28/0.55  fof(f101,plain,(
% 1.28/0.55    spl3_4 <=> v1_partfun1(sK1,sK0)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.28/0.55  fof(f64,plain,(
% 1.28/0.55    v4_relat_1(sK1,sK0)),
% 1.28/0.55    inference(resolution,[],[f44,f31])).
% 1.28/0.55  fof(f31,plain,(
% 1.28/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.55    inference(cnf_transformation,[],[f14])).
% 1.28/0.55  fof(f44,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f21])).
% 1.28/0.55  fof(f21,plain,(
% 1.28/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f5])).
% 1.28/0.55  fof(f5,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.55  fof(f266,plain,(
% 1.28/0.55    ~spl3_2 | spl3_24 | ~spl3_7 | ~spl3_8 | ~spl3_4 | ~spl3_14),
% 1.28/0.55    inference(avatar_split_clause,[],[f261,f191,f101,f128,f124,f263,f89])).
% 1.28/0.55  fof(f89,plain,(
% 1.28/0.55    spl3_2 <=> v1_funct_1(sK1)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.28/0.55  fof(f124,plain,(
% 1.28/0.55    spl3_7 <=> v1_relat_1(sK1)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.28/0.55  fof(f128,plain,(
% 1.28/0.55    spl3_8 <=> v4_relat_1(sK1,sK0)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.28/0.55  fof(f191,plain,(
% 1.28/0.55    spl3_14 <=> ! [X0] : (~m1_subset_1(sK2(X0,sK1),sK0) | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0))),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.28/0.55  fof(f261,plain,(
% 1.28/0.55    ~v1_partfun1(sK1,sK0) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0) | ~v1_funct_1(sK1) | ~spl3_14),
% 1.28/0.55    inference(duplicate_literal_removal,[],[f260])).
% 1.28/0.55  % (4784)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.55  fof(f260,plain,(
% 1.28/0.55    ~v1_partfun1(sK1,sK0) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0) | ~v1_funct_1(sK1) | ~v4_relat_1(sK1,sK0) | ~v1_partfun1(sK1,sK0) | ~spl3_14),
% 1.28/0.55    inference(resolution,[],[f192,f82])).
% 1.28/0.55  fof(f82,plain,(
% 1.28/0.55    ( ! [X2,X1] : (m1_subset_1(sK2(X2,X1),X2) | ~v1_relat_1(X1) | k6_partfun1(X2) = X1 | ~v1_funct_1(X1) | ~v4_relat_1(X1,X2) | ~v1_partfun1(X1,X2)) )),
% 1.28/0.55    inference(duplicate_literal_removal,[],[f81])).
% 1.28/0.55  fof(f81,plain,(
% 1.28/0.55    ( ! [X2,X1] : (m1_subset_1(sK2(X2,X1),X2) | ~v1_relat_1(X1) | k6_partfun1(X2) = X1 | ~v1_funct_1(X1) | ~v4_relat_1(X1,X2) | ~v1_relat_1(X1) | ~v1_partfun1(X1,X2)) )),
% 1.28/0.55    inference(superposition,[],[f76,f42])).
% 1.28/0.55  fof(f42,plain,(
% 1.28/0.55    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_partfun1(X1,X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f19])).
% 1.28/0.55  fof(f19,plain,(
% 1.28/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.28/0.55    inference(flattening,[],[f18])).
% 1.28/0.55  fof(f18,plain,(
% 1.28/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.28/0.55    inference(ennf_transformation,[],[f6])).
% 1.28/0.55  fof(f6,axiom,(
% 1.28/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.28/0.55  fof(f76,plain,(
% 1.28/0.55    ( ! [X0] : (m1_subset_1(sK2(k1_relat_1(X0),X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | k6_partfun1(k1_relat_1(X0)) = X0 | ~v1_funct_1(X0)) )),
% 1.28/0.55    inference(resolution,[],[f58,f36])).
% 1.28/0.55  fof(f36,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f15])).
% 1.28/0.55  fof(f15,plain,(
% 1.28/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.28/0.55    inference(ennf_transformation,[],[f2])).
% 1.28/0.55  fof(f2,axiom,(
% 1.28/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.28/0.55  fof(f58,plain,(
% 1.28/0.55    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 1.28/0.55    inference(equality_resolution,[],[f54])).
% 1.28/0.55  fof(f54,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK2(X0,X1),X0) | k6_partfun1(X0) = X1) )),
% 1.28/0.55    inference(definition_unfolding,[],[f37,f35])).
% 1.28/0.55  fof(f35,plain,(
% 1.28/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f8])).
% 1.28/0.55  fof(f8,axiom,(
% 1.28/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.28/0.55  fof(f37,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK2(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 1.28/0.55    inference(cnf_transformation,[],[f17])).
% 1.28/0.55  fof(f17,plain,(
% 1.28/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.55    inference(flattening,[],[f16])).
% 1.28/0.55  fof(f16,plain,(
% 1.28/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.55    inference(ennf_transformation,[],[f3])).
% 1.28/0.55  fof(f3,axiom,(
% 1.28/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.28/0.55  fof(f192,plain,(
% 1.28/0.55    ( ! [X0] : (~m1_subset_1(sK2(X0,sK1),sK0) | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0)) ) | ~spl3_14),
% 1.28/0.55    inference(avatar_component_clause,[],[f191])).
% 1.28/0.55  fof(f241,plain,(
% 1.28/0.55    ~spl3_7 | spl3_14 | spl3_12),
% 1.28/0.55    inference(avatar_split_clause,[],[f240,f181,f191,f124])).
% 1.28/0.55  fof(f181,plain,(
% 1.28/0.55    spl3_12 <=> m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.28/0.55  fof(f240,plain,(
% 1.28/0.55    ( ! [X0] : (~m1_subset_1(sK2(X0,sK1),sK0) | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v1_partfun1(sK1,X0)) ) | spl3_12),
% 1.28/0.55    inference(superposition,[],[f183,f42])).
% 1.28/0.55  fof(f183,plain,(
% 1.28/0.55    ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | spl3_12),
% 1.28/0.55    inference(avatar_component_clause,[],[f181])).
% 1.28/0.55  fof(f239,plain,(
% 1.28/0.55    ~spl3_7 | spl3_21 | spl3_13),
% 1.28/0.55    inference(avatar_split_clause,[],[f235,f185,f237,f124])).
% 1.28/0.55  fof(f185,plain,(
% 1.28/0.55    spl3_13 <=> sK1 = k6_partfun1(k1_relat_1(sK1))),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.28/0.55  fof(f235,plain,(
% 1.28/0.55    ( ! [X0] : (k6_partfun1(X0) != sK1 | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v1_partfun1(sK1,X0)) ) | spl3_13),
% 1.28/0.55    inference(superposition,[],[f186,f42])).
% 1.28/0.55  fof(f186,plain,(
% 1.28/0.55    sK1 != k6_partfun1(k1_relat_1(sK1)) | spl3_13),
% 1.28/0.55    inference(avatar_component_clause,[],[f185])).
% 1.28/0.55  fof(f225,plain,(
% 1.28/0.55    ~spl3_8 | ~spl3_4 | ~spl3_1 | ~spl3_15),
% 1.28/0.55    inference(avatar_split_clause,[],[f219,f199,f85,f101,f128])).
% 1.28/0.55  fof(f85,plain,(
% 1.28/0.55    spl3_1 <=> r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.28/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.28/0.56  fof(f199,plain,(
% 1.28/0.56    spl3_15 <=> ! [X0] : (k6_partfun1(X0) = sK1 | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0))),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.50/0.56  fof(f219,plain,(
% 1.50/0.56    ~r2_funct_2(sK0,sK0,sK1,sK1) | ~v1_partfun1(sK1,sK0) | ~v4_relat_1(sK1,sK0) | ~spl3_15),
% 1.50/0.56    inference(superposition,[],[f32,f200])).
% 1.50/0.56  fof(f200,plain,(
% 1.50/0.56    ( ! [X0] : (k6_partfun1(X0) = sK1 | ~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0)) ) | ~spl3_15),
% 1.50/0.56    inference(avatar_component_clause,[],[f199])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f201,plain,(
% 1.50/0.56    ~spl3_7 | spl3_15 | ~spl3_13),
% 1.50/0.56    inference(avatar_split_clause,[],[f194,f185,f199,f124])).
% 1.50/0.56  fof(f194,plain,(
% 1.50/0.56    ( ! [X0] : (k6_partfun1(X0) = sK1 | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v1_partfun1(sK1,X0)) ) | ~spl3_13),
% 1.50/0.56    inference(superposition,[],[f187,f42])).
% 1.50/0.56  fof(f187,plain,(
% 1.50/0.56    sK1 = k6_partfun1(k1_relat_1(sK1)) | ~spl3_13),
% 1.50/0.56    inference(avatar_component_clause,[],[f185])).
% 1.50/0.56  fof(f188,plain,(
% 1.50/0.56    ~spl3_12 | spl3_13 | ~spl3_7 | ~spl3_2 | ~spl3_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f179,f167,f89,f124,f185,f181])).
% 1.50/0.56  fof(f167,plain,(
% 1.50/0.56    spl3_11 <=> ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.50/0.56  fof(f179,plain,(
% 1.50/0.56    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(k1_relat_1(sK1)) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | ~spl3_11),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f178])).
% 1.50/0.56  fof(f178,plain,(
% 1.50/0.56    sK2(k1_relat_1(sK1),sK1) != sK2(k1_relat_1(sK1),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(k1_relat_1(sK1)) | ~m1_subset_1(sK2(k1_relat_1(sK1),sK1),sK0) | ~spl3_11),
% 1.50/0.56    inference(superposition,[],[f57,f168])).
% 1.50/0.56  fof(f168,plain,(
% 1.50/0.56    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0)) ) | ~spl3_11),
% 1.50/0.56    inference(avatar_component_clause,[],[f167])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 1.50/0.56    inference(equality_resolution,[],[f53])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k6_partfun1(X0) = X1) )),
% 1.50/0.56    inference(definition_unfolding,[],[f38,f35])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k6_relat_1(X0) = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f172,plain,(
% 1.50/0.56    spl3_10),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f171])).
% 1.50/0.56  fof(f171,plain,(
% 1.50/0.56    $false | spl3_10),
% 1.50/0.56    inference(subsumption_resolution,[],[f31,f165])).
% 1.50/0.56  fof(f165,plain,(
% 1.50/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_10),
% 1.50/0.56    inference(avatar_component_clause,[],[f163])).
% 1.50/0.56  fof(f163,plain,(
% 1.50/0.56    spl3_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.50/0.56  fof(f170,plain,(
% 1.50/0.56    spl3_9 | ~spl3_10 | ~spl3_3 | ~spl3_2 | spl3_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f156,f167,f89,f93,f163,f159])).
% 1.50/0.56  fof(f93,plain,(
% 1.50/0.56    spl3_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.50/0.56  fof(f156,plain,(
% 1.50/0.56    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_xboole_0(sK0)) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f155])).
% 1.50/0.56  fof(f155,plain,(
% 1.50/0.56    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~m1_subset_1(X0,sK0) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.50/0.56    inference(superposition,[],[f28,f48])).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ( ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f145,plain,(
% 1.50/0.56    spl3_8),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f142])).
% 1.50/0.56  fof(f142,plain,(
% 1.50/0.56    $false | spl3_8),
% 1.50/0.56    inference(subsumption_resolution,[],[f64,f130])).
% 1.50/0.56  fof(f130,plain,(
% 1.50/0.56    ~v4_relat_1(sK1,sK0) | spl3_8),
% 1.50/0.56    inference(avatar_component_clause,[],[f128])).
% 1.50/0.56  fof(f135,plain,(
% 1.50/0.56    spl3_7),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f132])).
% 1.50/0.56  fof(f132,plain,(
% 1.50/0.56    $false | spl3_7),
% 1.50/0.56    inference(subsumption_resolution,[],[f63,f126])).
% 1.50/0.56  fof(f126,plain,(
% 1.50/0.56    ~v1_relat_1(sK1) | spl3_7),
% 1.50/0.56    inference(avatar_component_clause,[],[f124])).
% 1.50/0.56  fof(f63,plain,(
% 1.50/0.56    v1_relat_1(sK1)),
% 1.50/0.56    inference(resolution,[],[f43,f31])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  % (4793)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.56  fof(f118,plain,(
% 1.50/0.56    ~spl3_5),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f117])).
% 1.50/0.56  fof(f117,plain,(
% 1.50/0.56    $false | ~spl3_5),
% 1.50/0.56    inference(subsumption_resolution,[],[f34,f114])).
% 1.50/0.56  fof(f114,plain,(
% 1.50/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 1.50/0.56    inference(superposition,[],[f33,f107])).
% 1.50/0.56  fof(f107,plain,(
% 1.50/0.56    k1_xboole_0 = sK0 | ~spl3_5),
% 1.50/0.56    inference(avatar_component_clause,[],[f105])).
% 1.50/0.56  fof(f105,plain,(
% 1.50/0.56    spl3_5 <=> k1_xboole_0 = sK0),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    v1_xboole_0(k1_xboole_0)),
% 1.50/0.56    inference(cnf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    v1_xboole_0(k1_xboole_0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.50/0.56  fof(f110,plain,(
% 1.50/0.56    spl3_3),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f109])).
% 1.50/0.56  fof(f109,plain,(
% 1.50/0.56    $false | spl3_3),
% 1.50/0.56    inference(subsumption_resolution,[],[f30,f95])).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    ~v1_funct_2(sK1,sK0,sK0) | spl3_3),
% 1.50/0.56    inference(avatar_component_clause,[],[f93])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    v1_funct_2(sK1,sK0,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f108,plain,(
% 1.50/0.56    spl3_4 | spl3_5 | ~spl3_2 | ~spl3_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f99,f93,f89,f105,f101])).
% 1.50/0.56  fof(f99,plain,(
% 1.50/0.56    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_xboole_0 = sK0 | v1_partfun1(sK1,sK0)),
% 1.50/0.56    inference(resolution,[],[f46,f31])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.50/0.56    inference(flattening,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.50/0.56  fof(f98,plain,(
% 1.50/0.56    spl3_2),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f97])).
% 1.50/0.56  fof(f97,plain,(
% 1.50/0.56    $false | spl3_2),
% 1.50/0.56    inference(subsumption_resolution,[],[f29,f91])).
% 1.50/0.56  fof(f91,plain,(
% 1.50/0.56    ~v1_funct_1(sK1) | spl3_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f89])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    v1_funct_1(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f96,plain,(
% 1.50/0.56    spl3_1 | ~spl3_2 | ~spl3_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f83,f93,f89,f85])).
% 1.50/0.56  fof(f83,plain,(
% 1.50/0.56    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.50/0.56    inference(resolution,[],[f62,f31])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f61])).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.50/0.56    inference(equality_resolution,[],[f49])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.50/0.56    inference(flattening,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.50/0.56    inference(ennf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (4791)------------------------------
% 1.50/0.56  % (4791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (4791)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (4791)Memory used [KB]: 6396
% 1.50/0.56  % (4791)Time elapsed: 0.124 s
% 1.50/0.56  % (4791)------------------------------
% 1.50/0.56  % (4791)------------------------------
% 1.50/0.56  % (4777)Success in time 0.189 s
%------------------------------------------------------------------------------
