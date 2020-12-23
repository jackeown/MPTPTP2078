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
% DateTime   : Thu Dec  3 12:58:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 190 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  338 ( 522 expanded)
%              Number of equality atoms :   38 (  60 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7175)Refutation not found, incomplete strategy% (7175)------------------------------
% (7175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7175)Termination reason: Refutation not found, incomplete strategy

% (7175)Memory used [KB]: 6140
% (7175)Time elapsed: 0.037 s
% (7175)------------------------------
% (7175)------------------------------
fof(f533,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f74,f80,f84,f88,f92,f96,f100,f104,f136,f154,f172,f214,f232,f261,f281,f316,f520,f532])).

fof(f532,plain,
    ( ~ spl6_12
    | ~ spl6_44
    | ~ spl6_69 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_44
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f526,f315])).

fof(f315,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl6_44
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f526,plain,
    ( ~ r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_12
    | ~ spl6_69 ),
    inference(resolution,[],[f519,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK5(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK5(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f519,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl6_69
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f520,plain,
    ( spl6_69
    | ~ spl6_14
    | spl6_38 ),
    inference(avatar_split_clause,[],[f287,f279,f98,f518])).

fof(f98,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f279,plain,
    ( spl6_38
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f287,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_14
    | spl6_38 ),
    inference(resolution,[],[f280,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f280,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f279])).

fof(f316,plain,
    ( spl6_44
    | ~ spl6_15
    | spl6_38 ),
    inference(avatar_split_clause,[],[f286,f279,f102,f314])).

fof(f102,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f286,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_15
    | spl6_38 ),
    inference(resolution,[],[f280,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f281,plain,
    ( ~ spl6_38
    | ~ spl6_2
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f266,f259,f48,f279])).

fof(f48,plain,
    ( spl6_2
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r1_xboole_0(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f259,plain,
    ( spl6_34
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f266,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_34 ),
    inference(resolution,[],[f260,f49])).

fof(f49,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r1_xboole_0(X1,sK0) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f260,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl6_34
    | ~ spl6_11
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f239,f230,f86,f259])).

fof(f86,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r2_hidden(sK5(X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f230,plain,
    ( spl6_32
  <=> r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f239,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_11
    | ~ spl6_32 ),
    inference(resolution,[],[f231,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r2_hidden(sK5(X1),X1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f231,plain,
    ( r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( spl6_32
    | ~ spl6_15
    | spl6_29 ),
    inference(avatar_split_clause,[],[f219,f212,f102,f230])).

fof(f212,plain,
    ( spl6_29
  <=> r1_xboole_0(sK1(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f219,plain,
    ( r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0)
    | ~ spl6_15
    | spl6_29 ),
    inference(resolution,[],[f213,f103])).

fof(f213,plain,
    ( ~ r1_xboole_0(sK1(k1_xboole_0,sK0),sK0)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( ~ spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f197,f170,f48,f44,f212])).

fof(f44,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f170,plain,
    ( spl6_27
  <=> ! [X5] :
        ( k1_xboole_0 = X5
        | r2_hidden(sK1(k1_xboole_0,X5),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f197,plain,
    ( ~ r1_xboole_0(sK1(k1_xboole_0,sK0),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f190,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f190,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK1(k1_xboole_0,sK0),sK0)
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(resolution,[],[f171,f49])).

fof(f171,plain,
    ( ! [X5] :
        ( r2_hidden(sK1(k1_xboole_0,X5),X5)
        | k1_xboole_0 = X5 )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl6_27
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f164,f152,f82,f52,f170])).

fof(f52,plain,
    ( spl6_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f82,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f152,plain,
    ( spl6_24
  <=> ! [X2] :
        ( k1_xboole_0 = X2
        | r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0)
        | r2_hidden(sK1(k1_xboole_0,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f164,plain,
    ( ! [X5] :
        ( k1_xboole_0 = X5
        | r2_hidden(sK1(k1_xboole_0,X5),X5) )
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f53,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f163,plain,
    ( ! [X5] :
        ( k1_xboole_0 = X5
        | r2_hidden(sK1(k1_xboole_0,X5),X5)
        | ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,X5)) )
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(resolution,[],[f153,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f153,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0)
        | k1_xboole_0 = X2
        | r2_hidden(sK1(k1_xboole_0,X2),X2) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl6_24
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f146,f134,f94,f78,f72,f68,f152])).

fof(f68,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f72,plain,
    ( spl6_8
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f78,plain,
    ( spl6_9
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f94,plain,
    ( spl6_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f134,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f146,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0)
        | r2_hidden(sK1(k1_xboole_0,X2),X2) )
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f145,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f145,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0)
        | r2_hidden(sK1(k1_xboole_0,X2),X2)
        | k2_relat_1(k1_xboole_0) = X2 )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f144,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f144,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_xboole_0,X2),k1_relat_1(k1_xboole_0))
        | r2_hidden(sK1(k1_xboole_0,X2),X2)
        | k2_relat_1(k1_xboole_0) = X2 )
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f142,f95])).

fof(f95,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f142,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k1_xboole_0)
        | r2_hidden(sK3(k1_xboole_0,X2),k1_relat_1(k1_xboole_0))
        | r2_hidden(sK1(k1_xboole_0,X2),X2)
        | k2_relat_1(k1_xboole_0) = X2 )
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(resolution,[],[f135,f79])).

fof(f79,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f27,f134])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f104,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f34,f102])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f100,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f33,f98])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,
    ( spl6_13
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f76,f64,f56,f94])).

fof(f56,plain,
    ( spl6_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f64,plain,
    ( spl6_6
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

% (7166)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f76,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(superposition,[],[f57,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f57,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f92,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK5(X1)) ) ),
    inference(condensation,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,sK5(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f88,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f80,plain,
    ( spl6_9
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f75,f64,f60,f78])).

fof(f60,plain,
    ( spl6_5
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f75,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(superposition,[],[f61,f65])).

fof(f61,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f74,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f70,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f21,f68])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f64])).

fof(f20,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f62,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f58,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f46,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (7171)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (7161)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (7163)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (7171)Refutation not found, incomplete strategy% (7171)------------------------------
% 0.22/0.47  % (7171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7171)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (7171)Memory used [KB]: 10618
% 0.22/0.47  % (7171)Time elapsed: 0.060 s
% 0.22/0.47  % (7171)------------------------------
% 0.22/0.47  % (7171)------------------------------
% 0.22/0.48  % (7169)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (7161)Refutation not found, incomplete strategy% (7161)------------------------------
% 0.22/0.48  % (7161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7161)Memory used [KB]: 10618
% 0.22/0.48  % (7161)Time elapsed: 0.059 s
% 0.22/0.48  % (7161)------------------------------
% 0.22/0.48  % (7161)------------------------------
% 0.22/0.48  % (7163)Refutation not found, incomplete strategy% (7163)------------------------------
% 0.22/0.48  % (7163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7163)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7163)Memory used [KB]: 10746
% 0.22/0.48  % (7163)Time elapsed: 0.065 s
% 0.22/0.48  % (7163)------------------------------
% 0.22/0.48  % (7163)------------------------------
% 0.22/0.49  % (7164)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (7175)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (7169)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  % (7175)Refutation not found, incomplete strategy% (7175)------------------------------
% 0.22/0.49  % (7175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7175)Memory used [KB]: 6140
% 0.22/0.49  % (7175)Time elapsed: 0.037 s
% 0.22/0.49  % (7175)------------------------------
% 0.22/0.49  % (7175)------------------------------
% 0.22/0.49  fof(f533,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f74,f80,f84,f88,f92,f96,f100,f104,f136,f154,f172,f214,f232,f261,f281,f316,f520,f532])).
% 0.22/0.49  fof(f532,plain,(
% 0.22/0.49    ~spl6_12 | ~spl6_44 | ~spl6_69),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f531])).
% 0.22/0.49  fof(f531,plain,(
% 0.22/0.49    $false | (~spl6_12 | ~spl6_44 | ~spl6_69)),
% 0.22/0.49    inference(subsumption_resolution,[],[f526,f315])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~spl6_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f314])).
% 0.22/0.49  fof(f314,plain,(
% 0.22/0.49    spl6_44 <=> r2_hidden(sK4(sK5(sK0),sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.49  fof(f526,plain,(
% 0.22/0.49    ~r2_hidden(sK4(sK5(sK0),sK0),sK0) | (~spl6_12 | ~spl6_69)),
% 0.22/0.49    inference(resolution,[],[f519,f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK5(X1)) | ~r2_hidden(X0,X1)) ) | ~spl6_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    spl6_12 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK5(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.49  fof(f519,plain,(
% 0.22/0.49    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | ~spl6_69),
% 0.22/0.49    inference(avatar_component_clause,[],[f518])).
% 0.22/0.49  fof(f518,plain,(
% 0.22/0.49    spl6_69 <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 0.22/0.49  fof(f520,plain,(
% 0.22/0.49    spl6_69 | ~spl6_14 | spl6_38),
% 0.22/0.49    inference(avatar_split_clause,[],[f287,f279,f98,f518])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl6_14 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    spl6_38 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | (~spl6_14 | spl6_38)),
% 0.22/0.49    inference(resolution,[],[f280,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) ) | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    ~r1_xboole_0(sK5(sK0),sK0) | spl6_38),
% 0.22/0.49    inference(avatar_component_clause,[],[f279])).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    spl6_44 | ~spl6_15 | spl6_38),
% 0.22/0.49    inference(avatar_split_clause,[],[f286,f279,f102,f314])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl6_15 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    r2_hidden(sK4(sK5(sK0),sK0),sK0) | (~spl6_15 | spl6_38)),
% 0.22/0.49    inference(resolution,[],[f280,f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) ) | ~spl6_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    ~spl6_38 | ~spl6_2 | ~spl6_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f266,f259,f48,f279])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl6_2 <=> ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    spl6_34 <=> r2_hidden(sK5(sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    ~r1_xboole_0(sK5(sK0),sK0) | (~spl6_2 | ~spl6_34)),
% 0.22/0.49    inference(resolution,[],[f260,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) ) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    r2_hidden(sK5(sK0),sK0) | ~spl6_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f259])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    spl6_34 | ~spl6_11 | ~spl6_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f239,f230,f86,f259])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl6_11 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl6_32 <=> r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    r2_hidden(sK5(sK0),sK0) | (~spl6_11 | ~spl6_32)),
% 0.22/0.49    inference(resolution,[],[f231,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) ) | ~spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0) | ~spl6_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    spl6_32 | ~spl6_15 | spl6_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f219,f212,f102,f230])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    spl6_29 <=> r1_xboole_0(sK1(k1_xboole_0,sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1(k1_xboole_0,sK0),sK0),sK0) | (~spl6_15 | spl6_29)),
% 0.22/0.49    inference(resolution,[],[f213,f103])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    ~r1_xboole_0(sK1(k1_xboole_0,sK0),sK0) | spl6_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f212])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ~spl6_29 | spl6_1 | ~spl6_2 | ~spl6_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f197,f170,f48,f44,f212])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl6_1 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl6_27 <=> ! [X5] : (k1_xboole_0 = X5 | r2_hidden(sK1(k1_xboole_0,X5),X5))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ~r1_xboole_0(sK1(k1_xboole_0,sK0),sK0) | (spl6_1 | ~spl6_2 | ~spl6_27)),
% 0.22/0.49    inference(subsumption_resolution,[],[f190,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~r1_xboole_0(sK1(k1_xboole_0,sK0),sK0) | (~spl6_2 | ~spl6_27)),
% 0.22/0.49    inference(resolution,[],[f171,f49])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ( ! [X5] : (r2_hidden(sK1(k1_xboole_0,X5),X5) | k1_xboole_0 = X5) ) | ~spl6_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f170])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    spl6_27 | ~spl6_3 | ~spl6_10 | ~spl6_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f164,f152,f82,f52,f170])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl6_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl6_10 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl6_24 <=> ! [X2] : (k1_xboole_0 = X2 | r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X2),X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    ( ! [X5] : (k1_xboole_0 = X5 | r2_hidden(sK1(k1_xboole_0,X5),X5)) ) | (~spl6_3 | ~spl6_10 | ~spl6_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f163,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ( ! [X5] : (k1_xboole_0 = X5 | r2_hidden(sK1(k1_xboole_0,X5),X5) | ~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,X5))) ) | (~spl6_10 | ~spl6_24)),
% 0.22/0.49    inference(resolution,[],[f153,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0) | k1_xboole_0 = X2 | r2_hidden(sK1(k1_xboole_0,X2),X2)) ) | ~spl6_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl6_24 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_13 | ~spl6_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f146,f134,f94,f78,f72,f68,f152])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl6_7 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl6_8 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl6_9 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl6_13 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl6_21 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X2] : (k1_xboole_0 = X2 | r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X2),X2)) ) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_13 | ~spl6_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f145,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(sK3(k1_xboole_0,X2),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X2),X2) | k2_relat_1(k1_xboole_0) = X2) ) | (~spl6_7 | ~spl6_9 | ~spl6_13 | ~spl6_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f144,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(sK3(k1_xboole_0,X2),k1_relat_1(k1_xboole_0)) | r2_hidden(sK1(k1_xboole_0,X2),X2) | k2_relat_1(k1_xboole_0) = X2) ) | (~spl6_9 | ~spl6_13 | ~spl6_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f142,f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | ~spl6_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f94])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_relat_1(k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X2),k1_relat_1(k1_xboole_0)) | r2_hidden(sK1(k1_xboole_0,X2),X2) | k2_relat_1(k1_xboole_0) = X2) ) | (~spl6_9 | ~spl6_21)),
% 0.22/0.49    inference(resolution,[],[f135,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    v1_funct_1(k1_xboole_0) | ~spl6_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f78])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) ) | ~spl6_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl6_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f134])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl6_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f102])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl6_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f98])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl6_13 | ~spl6_4 | ~spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f76,f64,f56,f94])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl6_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl6_6 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  % (7166)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | (~spl6_4 | ~spl6_6)),
% 0.22/0.49    inference(superposition,[],[f57,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl6_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f90])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK5(X1))) )),
% 0.22/0.49    inference(condensation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,sK5(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl6_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f86])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl6_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f82])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl6_9 | ~spl6_5 | ~spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f75,f64,f60,f78])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl6_5 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    v1_funct_1(k1_xboole_0) | (~spl6_5 | ~spl6_6)),
% 0.22/0.49    inference(superposition,[],[f61,f65])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f72])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f68])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f64])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f60])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl6_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f56])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f52])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f48])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    k1_xboole_0 != sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (7169)------------------------------
% 0.22/0.49  % (7169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7169)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (7169)Memory used [KB]: 10874
% 0.22/0.49  % (7169)Time elapsed: 0.080 s
% 0.22/0.49  % (7169)------------------------------
% 0.22/0.49  % (7169)------------------------------
% 0.22/0.49  % (7165)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (7159)Success in time 0.133 s
%------------------------------------------------------------------------------
