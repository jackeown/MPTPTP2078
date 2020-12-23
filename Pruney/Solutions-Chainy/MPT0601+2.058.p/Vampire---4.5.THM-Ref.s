%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 278 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  286 (1034 expanded)
%              Number of equality atoms :   59 ( 276 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f48,f52,f108,f155,f173,f175,f200,f204,f219,f233,f235,f256,f281])).

fof(f281,plain,
    ( spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f263,f253,f86])).

fof(f86,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f253,plain,
    ( spl5_24
  <=> r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f263,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_24 ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_24 ),
    inference(superposition,[],[f254,f58])).

fof(f58,plain,(
    ! [X3] :
      ( k1_xboole_0 = k1_relat_1(X3)
      | r2_hidden(k4_tarski(sK2(X3,k1_xboole_0),sK3(X3,k1_xboole_0)),X3) ) ),
    inference(resolution,[],[f28,f53])).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f25,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f17,f16,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f254,plain,
    ( r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f256,plain,
    ( spl5_24
    | spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f250,f231,f93,f253])).

fof(f93,plain,
    ( spl5_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f231,plain,
    ( spl5_23
  <=> k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f250,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ spl5_23 ),
    inference(superposition,[],[f58,f232])).

fof(f232,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f231])).

fof(f235,plain,
    ( spl5_1
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl5_1
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f41,f218])).

fof(f218,plain,
    ( ! [X2] : r2_hidden(X2,k1_relat_1(sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl5_21
  <=> ! [X2] : r2_hidden(X2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f233,plain,
    ( spl5_23
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f225,f214,f231])).

fof(f214,plain,
    ( spl5_20
  <=> ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f225,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(resolution,[],[f215,f67])).

fof(f67,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(sK2(X5,k1_relat_1(k1_xboole_0)),sK3(X5,k1_relat_1(k1_xboole_0))),X5)
      | k1_relat_1(X5) = k1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f59,f53])).

fof(f59,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK2(X4,k1_relat_1(X5)),sK4(X5,sK2(X4,k1_relat_1(X5)))),X5)
      | k1_relat_1(X5) = k1_relat_1(X4)
      | r2_hidden(k4_tarski(sK2(X4,k1_relat_1(X5)),sK3(X4,k1_relat_1(X5))),X4) ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f215,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f219,plain,
    ( spl5_20
    | spl5_21
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f208,f202,f217,f214])).

fof(f202,plain,
    ( spl5_18
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X5,k1_relat_1(k1_xboole_0))
        | r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X4,X5),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f208,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(k1_xboole_0)) )
    | ~ spl5_18 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
        | r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f203,f35])).

fof(f35,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f203,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),sK1)
        | r2_hidden(X4,k1_relat_1(sK1))
        | ~ r2_hidden(X5,k1_relat_1(k1_xboole_0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( ~ spl5_3
    | spl5_18
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f197,f50,f202,f50])).

fof(f50,plain,
    ( spl5_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f197,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k1_relat_1(k1_xboole_0))
        | r2_hidden(k4_tarski(X4,X5),sK1)
        | ~ v1_relat_1(sK1)
        | r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f34,f138])).

% (32162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f138,plain,
    ( ! [X6] :
        ( k1_relat_1(k1_xboole_0) = k11_relat_1(sK1,X6)
        | r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f133,f53])).

fof(f133,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK2(X2,k11_relat_1(sK1,X3)),sK3(X2,k11_relat_1(sK1,X3))),X2)
        | k1_relat_1(X2) = k11_relat_1(sK1,X3)
        | r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f131,f35])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK2(X1,k11_relat_1(sK1,X0))),sK1)
        | k1_relat_1(X1) = k11_relat_1(sK1,X0)
        | r2_hidden(k4_tarski(sK2(X1,k11_relat_1(sK1,X0)),sK3(X1,k11_relat_1(sK1,X0))),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X7)
      | k11_relat_1(X7,X8) = k1_relat_1(X6)
      | r2_hidden(k4_tarski(X8,sK2(X6,k11_relat_1(X7,X8))),X7)
      | r2_hidden(k4_tarski(sK2(X6,k11_relat_1(X7,X8)),sK3(X6,k11_relat_1(X7,X8))),X6) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f200,plain,
    ( spl5_1
    | ~ spl5_6
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f196,f50,f43,f93,f40])).

fof(f43,plain,
    ( spl5_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f196,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r2_hidden(sK0,k1_relat_1(sK1))
    | spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f47,f138])).

fof(f47,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f175,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f53])).

fof(f172,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_14
  <=> r2_hidden(sK4(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f173,plain,
    ( ~ spl5_3
    | spl5_14
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f168,f153,f43,f171,f50])).

fof(f153,plain,
    ( spl5_11
  <=> r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f168,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f166,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f166,plain,
    ( r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f154,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f150,f40,f153])).

fof(f150,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f46,f36])).

fof(f46,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f108,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f87,f53])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f52,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f48,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f23,f43,f40])).

fof(f23,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f24,f43,f40])).

fof(f24,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (32163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (32173)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (32163)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (32164)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (32172)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (32175)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f45,f48,f52,f108,f155,f173,f175,f200,f204,f219,f233,f235,f256,f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    spl5_4 | ~spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f263,f253,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl5_4 <=> r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    spl5_24 <=> r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_24),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f262])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_24),
% 0.21/0.48    inference(superposition,[],[f254,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X3] : (k1_xboole_0 = k1_relat_1(X3) | r2_hidden(k4_tarski(sK2(X3,k1_xboole_0),sK3(X3,k1_xboole_0)),X3)) )),
% 0.21/0.48    inference(resolution,[],[f28,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f25,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f17,f16,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl5_24 | spl5_6 | ~spl5_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f250,f231,f93,f253])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl5_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl5_23 <=> k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),sK3(k1_relat_1(k1_xboole_0),k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~spl5_23),
% 0.21/0.49    inference(superposition,[],[f58,f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0)) | ~spl5_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl5_1 | ~spl5_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl5_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl5_21 <=> ! [X2] : r2_hidden(X2,k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl5_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl5_23 | ~spl5_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f225,f214,f231])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl5_20 <=> ! [X3] : ~r2_hidden(X3,k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0)) | ~spl5_20),
% 0.21/0.49    inference(resolution,[],[f215,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X5] : (r2_hidden(k4_tarski(sK2(X5,k1_relat_1(k1_xboole_0)),sK3(X5,k1_relat_1(k1_xboole_0))),X5) | k1_relat_1(X5) = k1_relat_1(k1_xboole_0)) )),
% 0.21/0.49    inference(resolution,[],[f59,f53])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X4,X5] : (r2_hidden(k4_tarski(sK2(X4,k1_relat_1(X5)),sK4(X5,sK2(X4,k1_relat_1(X5)))),X5) | k1_relat_1(X5) = k1_relat_1(X4) | r2_hidden(k4_tarski(sK2(X4,k1_relat_1(X5)),sK3(X4,k1_relat_1(X5))),X4)) )),
% 0.21/0.49    inference(resolution,[],[f28,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0))) ) | ~spl5_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f214])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl5_20 | spl5_21 | ~spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f202,f217,f214])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl5_18 <=> ! [X5,X4] : (~r2_hidden(X5,k1_relat_1(k1_xboole_0)) | r2_hidden(X4,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X4,X5),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k1_xboole_0))) ) | ~spl5_18),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k1_xboole_0)) | r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl5_18),
% 0.21/0.49    inference(resolution,[],[f203,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(X4,k1_relat_1(sK1)) | ~r2_hidden(X5,k1_relat_1(k1_xboole_0))) ) | ~spl5_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f202])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~spl5_3 | spl5_18 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f197,f50,f202,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl5_3 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X5,k1_relat_1(k1_xboole_0)) | r2_hidden(k4_tarski(X4,X5),sK1) | ~v1_relat_1(sK1) | r2_hidden(X4,k1_relat_1(sK1))) ) | ~spl5_3),
% 0.21/0.49    inference(superposition,[],[f34,f138])).
% 0.21/0.49  % (32162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X6] : (k1_relat_1(k1_xboole_0) = k11_relat_1(sK1,X6) | r2_hidden(X6,k1_relat_1(sK1))) ) | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f133,f53])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK2(X2,k11_relat_1(sK1,X3)),sK3(X2,k11_relat_1(sK1,X3))),X2) | k1_relat_1(X2) = k11_relat_1(sK1,X3) | r2_hidden(X3,k1_relat_1(sK1))) ) | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f131,f35])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK2(X1,k11_relat_1(sK1,X0))),sK1) | k1_relat_1(X1) = k11_relat_1(sK1,X0) | r2_hidden(k4_tarski(sK2(X1,k11_relat_1(sK1,X0)),sK3(X1,k11_relat_1(sK1,X0))),X1)) ) | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f60,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (~v1_relat_1(X7) | k11_relat_1(X7,X8) = k1_relat_1(X6) | r2_hidden(k4_tarski(X8,sK2(X6,k11_relat_1(X7,X8))),X7) | r2_hidden(k4_tarski(sK2(X6,k11_relat_1(X7,X8)),sK3(X6,k11_relat_1(X7,X8))),X6)) )),
% 0.21/0.49    inference(resolution,[],[f28,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl5_1 | ~spl5_6 | spl5_2 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f196,f50,f43,f93,f40])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl5_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r2_hidden(sK0,k1_relat_1(sK1)) | (spl5_2 | ~spl5_3)),
% 0.21/0.49    inference(superposition,[],[f47,f138])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~spl5_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    $false | ~spl5_14),
% 0.21/0.49    inference(resolution,[],[f172,f53])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    r2_hidden(sK4(sK1,sK0),k1_xboole_0) | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl5_14 <=> r2_hidden(sK4(sK1,sK0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~spl5_3 | spl5_14 | ~spl5_2 | ~spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f153,f43,f171,f50])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl5_11 <=> r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    r2_hidden(sK4(sK1,sK0),k1_xboole_0) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f166,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl5_11),
% 0.21/0.49    inference(resolution,[],[f154,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f153])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl5_11 | ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f150,f40,f153])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f46,f36])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~spl5_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    $false | ~spl5_4),
% 0.21/0.49    inference(resolution,[],[f87,f53])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f43,f40])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~spl5_1 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f43,f40])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (32163)------------------------------
% 0.21/0.49  % (32163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32163)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (32163)Memory used [KB]: 10746
% 0.21/0.49  % (32163)Time elapsed: 0.059 s
% 0.21/0.49  % (32163)------------------------------
% 0.21/0.49  % (32163)------------------------------
% 0.21/0.49  % (32151)Success in time 0.133 s
%------------------------------------------------------------------------------
