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
% DateTime   : Thu Dec  3 12:52:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 224 expanded)
%              Number of leaves         :   28 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  465 ( 732 expanded)
%              Number of equality atoms :   81 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f90,f100,f105,f113,f127,f138,f171,f177,f210,f234,f294,f422,f423,f424,f434])).

fof(f434,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_18
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_18
    | spl5_19 ),
    inference(subsumption_resolution,[],[f427,f224])).

fof(f224,plain,
    ( sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_18
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f427,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_19 ),
    inference(subsumption_resolution,[],[f426,f61])).

fof(f61,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f426,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_funct_1(sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_19 ),
    inference(subsumption_resolution,[],[f425,f56])).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f425,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_19 ),
    inference(subsumption_resolution,[],[f302,f89])).

fof(f89,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f302,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_19 ),
    inference(superposition,[],[f233,f299])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k5_relat_1(k4_relat_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k4_relat_1(sK1),X1))
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f298,f137])).

fof(f137,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_11
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f297,f126])).

fof(f126,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_9
  <=> k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f296,f137])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(sK1)))
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f295,f170])).

fof(f170,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_13
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k4_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(sK1)))
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f117,f137])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k2_funct_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(sK1)))
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f112,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (19050)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (19053)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (19059)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (19059)Refutation not found, incomplete strategy% (19059)------------------------------
% (19059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19059)Termination reason: Refutation not found, incomplete strategy

% (19059)Memory used [KB]: 10618
% (19059)Time elapsed: 0.061 s
% (19059)------------------------------
% (19059)------------------------------
% (19048)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f112,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_8
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f233,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_19
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f424,plain,
    ( sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),sK0)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f423,plain,
    ( sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),sK0)
    | k2_funct_1(sK1) != k4_relat_1(sK1)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f422,plain,
    ( spl5_36
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f301,f291,f207,f135,f64,f59,f54,f419])).

fof(f419,plain,
    ( spl5_36
  <=> sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f64,plain,
    ( spl5_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f207,plain,
    ( spl5_16
  <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f291,plain,
    ( spl5_24
  <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f301,plain,
    ( sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_16
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f300,f209])).

fof(f209,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f300,plain,
    ( sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)
    | ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_24 ),
    inference(superposition,[],[f182,f293])).

fof(f293,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f291])).

fof(f182,plain,
    ( ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f81,f137])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f80,f56])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f66,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f294,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f198,f174,f59,f54,f291])).

fof(f174,plain,
    ( spl5_14
  <=> r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f198,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(resolution,[],[f176,f166])).

fof(f166,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
        | k1_funct_1(sK1,X8) = X9 )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f75,f61])).

fof(f75,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,X8) = X9
        | ~ r2_hidden(k4_tarski(X8,X9),sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f176,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f234,plain,
    ( ~ spl5_19
    | spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f141,f135,f93,f231])).

fof(f93,plain,
    ( spl5_5
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f141,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_5
    | ~ spl5_11 ),
    inference(superposition,[],[f95,f137])).

fof(f95,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f210,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f200,f174,f54,f207])).

fof(f200,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f176,f72])).

fof(f72,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f177,plain,
    ( spl5_14
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f106,f102,f174])).

fof(f102,plain,
    ( spl5_7
  <=> sP3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f104,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f104,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f171,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f144,f135,f59,f54,f168])).

fof(f144,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f142,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_11 ),
    inference(superposition,[],[f34,f137])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f138,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f85,f64,f59,f54,f135])).

fof(f85,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f84,f56])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f79,f61])).

fof(f79,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f127,plain,
    ( spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f68,f54,f124])).

fof(f68,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f113,plain,
    ( spl5_8
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f108,f59,f54,f110])).

fof(f108,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f70,f61])).

fof(f70,plain,
    ( ~ v1_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f91,f87,f102])).

fof(f91,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f89,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP3(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f100,plain,
    ( ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f26,f97,f93])).

fof(f97,plain,
    ( spl5_6
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f26,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f87])).

fof(f30,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (19045)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (19042)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (19040)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (19040)Refutation not found, incomplete strategy% (19040)------------------------------
% 0.20/0.47  % (19040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19040)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19040)Memory used [KB]: 10618
% 0.20/0.47  % (19040)Time elapsed: 0.052 s
% 0.20/0.47  % (19040)------------------------------
% 0.20/0.47  % (19040)------------------------------
% 0.20/0.47  % (19042)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f435,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f57,f62,f67,f90,f100,f105,f113,f127,f138,f171,f177,f210,f234,f294,f422,f423,f424,f434])).
% 0.20/0.47  fof(f434,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_18 | spl5_19),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f433])).
% 0.20/0.47  fof(f433,plain,(
% 0.20/0.47    $false | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_18 | spl5_19)),
% 0.20/0.47    inference(subsumption_resolution,[],[f427,f224])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~spl5_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f223])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    spl5_18 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.47  fof(f427,plain,(
% 0.20/0.47    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_19)),
% 0.20/0.47    inference(subsumption_resolution,[],[f426,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    v1_funct_1(sK1) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_2 <=> v1_funct_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f426,plain,(
% 0.20/0.47    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_funct_1(sK1) | (~spl5_1 | ~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_19)),
% 0.20/0.47    inference(subsumption_resolution,[],[f425,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    v1_relat_1(sK1) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl5_1 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f425,plain,(
% 0.20/0.47    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | (~spl5_4 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_19)),
% 0.20/0.47    inference(subsumption_resolution,[],[f302,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f302,plain,(
% 0.20/0.47    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | (~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_19)),
% 0.20/0.47    inference(superposition,[],[f233,f299])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_funct_1(k5_relat_1(k4_relat_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k4_relat_1(sK1),X1)) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | (~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f298,f137])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl5_11 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1))) ) | (~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f297,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) | ~spl5_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl5_9 <=> k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.47  fof(f297,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1))) ) | (~spl5_8 | ~spl5_11 | ~spl5_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f296,f137])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(sK1))) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1))) ) | (~spl5_8 | ~spl5_11 | ~spl5_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f295,f170])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    v1_funct_1(k4_relat_1(sK1)) | ~spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    spl5_13 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(sK1))) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1))) ) | (~spl5_8 | ~spl5_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f117,f137])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(sK1))) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X0),X1) = k1_funct_1(X0,k1_funct_1(k2_funct_1(sK1),X1))) ) | ~spl5_8),
% 0.20/0.47    inference(resolution,[],[f112,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  % (19050)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (19053)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (19059)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (19059)Refutation not found, incomplete strategy% (19059)------------------------------
% 0.20/0.48  % (19059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19059)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (19059)Memory used [KB]: 10618
% 0.20/0.48  % (19059)Time elapsed: 0.061 s
% 0.20/0.48  % (19059)------------------------------
% 0.20/0.48  % (19059)------------------------------
% 0.20/0.48  % (19048)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK1)) | ~spl5_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f110])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl5_8 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | spl5_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f231])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    spl5_19 <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.48  fof(f424,plain,(
% 0.20/0.48    sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),sK0) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f423,plain,(
% 0.20/0.48    sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),sK0) | k2_funct_1(sK1) != k4_relat_1(sK1) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f422,plain,(
% 0.20/0.48    spl5_36 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_16 | ~spl5_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f301,f291,f207,f135,f64,f59,f54,f419])).
% 0.20/0.48  fof(f419,plain,(
% 0.20/0.48    spl5_36 <=> sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl5_3 <=> v2_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    spl5_16 <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    spl5_24 <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_16 | ~spl5_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f300,f209])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | ~spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f207])).
% 0.20/0.48  fof(f300,plain,(
% 0.20/0.48    sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) | ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_24)),
% 0.20/0.48    inference(superposition,[],[f182,f293])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f291])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11)),
% 0.20/0.48    inference(forward_demodulation,[],[f81,f137])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f56])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f77,f61])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl5_3),
% 0.20/0.48    inference(resolution,[],[f66,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    v2_funct_1(sK1) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f294,plain,(
% 0.20/0.48    spl5_24 | ~spl5_1 | ~spl5_2 | ~spl5_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f198,f174,f59,f54,f291])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    spl5_14 <=> r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_14)),
% 0.20/0.48    inference(resolution,[],[f176,f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),sK1) | k1_funct_1(sK1,X8) = X9) ) | (~spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f75,f61])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~v1_funct_1(sK1) | k1_funct_1(sK1,X8) = X9 | ~r2_hidden(k4_tarski(X8,X9),sK1)) ) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f56,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) | ~spl5_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f174])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    ~spl5_19 | spl5_5 | ~spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f141,f135,f93,f231])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl5_5 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | (spl5_5 | ~spl5_11)),
% 0.20/0.48    inference(superposition,[],[f95,f137])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    spl5_16 | ~spl5_1 | ~spl5_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f200,f174,f54,f207])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_1 | ~spl5_14)),
% 0.20/0.48    inference(resolution,[],[f176,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f56,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    spl5_14 | ~spl5_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f106,f102,f174])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl5_7 <=> sP3(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) | ~spl5_7),
% 0.20/0.48    inference(resolution,[],[f104,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~sP3(X2,X0) | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    sP3(sK0,sK1) | ~spl5_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    spl5_13 | ~spl5_1 | ~spl5_2 | ~spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f144,f135,f59,f54,f168])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    v1_funct_1(k4_relat_1(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f143,f56])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f142,f61])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_11),
% 0.20/0.48    inference(superposition,[],[f34,f137])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl5_11 | ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f85,f64,f59,f54,f135])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f56])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f61])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_3),
% 0.20/0.48    inference(resolution,[],[f66,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl5_9 | ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f68,f54,f124])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f56,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl5_8 | ~spl5_1 | ~spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f108,f59,f54,f110])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK1)) | (~spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f70,f61])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~v1_funct_1(sK1) | v1_relat_1(k2_funct_1(sK1)) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f56,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl5_7 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f91,f87,f102])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    sP3(sK0,sK1) | ~spl5_4),
% 0.20/0.48    inference(resolution,[],[f89,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP3(X2,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ~spl5_5 | ~spl5_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f97,f93])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl5_6 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f87])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v2_funct_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f59])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v1_funct_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f54])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (19042)------------------------------
% 0.20/0.48  % (19042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19042)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (19042)Memory used [KB]: 10874
% 0.20/0.48  % (19042)Time elapsed: 0.062 s
% 0.20/0.48  % (19042)------------------------------
% 0.20/0.48  % (19042)------------------------------
% 0.20/0.48  % (19038)Success in time 0.127 s
%------------------------------------------------------------------------------
