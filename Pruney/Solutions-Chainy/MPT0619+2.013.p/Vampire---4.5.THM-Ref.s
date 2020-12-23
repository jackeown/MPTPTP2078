%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 205 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  328 ( 552 expanded)
%              Number of equality atoms :  125 ( 238 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f105,f110,f123,f131,f139,f149,f205,f227,f235,f242])).

fof(f242,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_18 ),
    inference(unit_resulting_resolution,[],[f77,f82,f102,f234,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f234,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_18
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f102,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f77,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f235,plain,
    ( ~ spl7_18
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f230,f225,f232])).

fof(f225,plain,
    ( spl7_17
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK0) != X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f230,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl7_17 ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) != X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( spl7_7
    | spl7_17
    | spl7_5
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f214,f203,f107,f225,f128])).

fof(f128,plain,
    ( spl7_7
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f107,plain,
    ( spl7_5
  <=> k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f203,plain,
    ( spl7_14
  <=> ! [X3] :
        ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3
        | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f214,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) != X0
        | k1_xboole_0 = k2_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl7_5
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) != X0
        | k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) != k2_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl7_5
    | ~ spl7_14 ),
    inference(superposition,[],[f133,f204])).

% (4934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f204,plain,
    ( ! [X3] :
        ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3
        | ~ r2_hidden(X3,k2_relat_1(sK1)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f203])).

fof(f133,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) != sK5(X1,k1_funct_1(sK1,sK0))
        | k1_xboole_0 = X1
        | k2_relat_1(sK1) != X1 )
    | spl7_5 ),
    inference(superposition,[],[f109,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (4947)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f109,plain,
    ( k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f205,plain,
    ( spl7_7
    | spl7_14
    | spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f158,f147,f107,f203,f128])).

fof(f147,plain,
    ( spl7_9
  <=> ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f158,plain,
    ( ! [X3] :
        ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3
        | ~ r2_hidden(X3,k2_relat_1(sK1))
        | k1_xboole_0 = k2_relat_1(sK1) )
    | spl7_5
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( ! [X3] :
        ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3
        | ~ r2_hidden(X3,k2_relat_1(sK1))
        | k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) != k2_relat_1(sK1) )
    | spl7_5
    | ~ spl7_9 ),
    inference(resolution,[],[f150,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,k1_funct_1(sK1,sK0)),X0)
        | k1_xboole_0 = X0
        | k2_relat_1(sK1) != X0 )
    | spl7_5 ),
    inference(superposition,[],[f109,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | X0 = X1
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_9 ),
    inference(superposition,[],[f148,f148])).

fof(f148,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_9
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f142,f137,f147,f80,f75])).

fof(f137,plain,
    ( spl7_8
  <=> ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f142,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(superposition,[],[f65,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f65,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f139,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f112,f85,f137,f80,f75])).

fof(f85,plain,
    ( spl7_3
  <=> k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f112,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | sK0 = X3 )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | sK0 = X3
        | sK0 = X3
        | sK0 = X3 )
    | ~ spl7_3 ),
    inference(superposition,[],[f73,f87])).

fof(f87,plain,
    ( k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

% (4940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f131,plain,
    ( ~ spl7_4
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f126,f120,f128,f75,f100])).

fof(f120,plain,
    ( spl7_6
  <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f126,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(superposition,[],[f36,f122])).

fof(f122,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f123,plain,
    ( ~ spl7_1
    | spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f117,f85,f120,f75])).

fof(f117,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(superposition,[],[f26,f93])).

fof(f93,plain,
    ( ! [X2] :
        ( k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1))
        | ~ v1_relat_1(X2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f52,f87])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f110,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f50,f107])).

fof(f50,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f24,f49])).

fof(f24,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f105,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f97,f85,f100])).

fof(f97,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_3 ),
    inference(superposition,[],[f68,f87])).

fof(f68,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f51,f85])).

fof(f51,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f49])).

fof(f23,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f22,f80])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f75])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (4946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (4930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (4927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (4938)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (4924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (4945)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (4931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (4926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (4946)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (4939)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (4937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (4943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (4950)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (4925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f78,f83,f88,f105,f110,f123,f131,f139,f149,f205,f227,f235,f242])).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_2 | ~spl7_4 | spl7_18),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | spl7_18)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f77,f82,f102,f234,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(equality_resolution,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl7_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f232])).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    spl7_18 <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    spl7_4 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    v1_funct_1(sK1) | ~spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    spl7_2 <=> v1_funct_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    spl7_1 <=> v1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    ~spl7_18 | ~spl7_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f230,f225,f232])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    spl7_17 <=> ! [X0] : (k1_funct_1(sK1,sK0) != X0 | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl7_17),
% 0.22/0.55    inference(equality_resolution,[],[f226])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) != X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f225])).
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    spl7_7 | spl7_17 | spl7_5 | ~spl7_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f214,f203,f107,f225,f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    spl7_7 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    spl7_5 <=> k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    spl7_14 <=> ! [X3] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3 | ~r2_hidden(X3,k2_relat_1(sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) != X0 | k1_xboole_0 = k2_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl7_5 | ~spl7_14)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f209])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) != X0 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl7_5 | ~spl7_14)),
% 0.22/0.55    inference(superposition,[],[f133,f204])).
% 0.22/0.55  % (4934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    ( ! [X3] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3 | ~r2_hidden(X3,k2_relat_1(sK1))) ) | ~spl7_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f203])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) != sK5(X1,k1_funct_1(sK1,sK0)) | k1_xboole_0 = X1 | k2_relat_1(sK1) != X1) ) | spl7_5),
% 0.22/0.55    inference(superposition,[],[f109,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.22/0.55    inference(definition_unfolding,[],[f38,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f25,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f34,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % (4947)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl7_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f107])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    spl7_7 | spl7_14 | spl7_5 | ~spl7_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f158,f147,f107,f203,f128])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    spl7_9 <=> ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ( ! [X3] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3 | ~r2_hidden(X3,k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1)) ) | (spl7_5 | ~spl7_9)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f156])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X3] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X3 | ~r2_hidden(X3,k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) != k2_relat_1(sK1)) ) | (spl7_5 | ~spl7_9)),
% 0.22/0.55    inference(resolution,[],[f150,f132])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK5(X0,k1_funct_1(sK1,sK0)),X0) | k1_xboole_0 = X0 | k2_relat_1(sK1) != X0) ) | spl7_5),
% 0.22/0.55    inference(superposition,[],[f109,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f37,f49])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | X0 = X1 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_9),
% 0.22/0.55    inference(superposition,[],[f148,f148])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f147])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_2 | spl7_9 | ~spl7_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f142,f137,f147,f80,f75])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl7_8 <=> ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_8),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f141])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_8),
% 0.22/0.55    inference(superposition,[],[f65,f138])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f137])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0] : (k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_2 | spl7_8 | ~spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f112,f85,f137,f80,f75])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl7_3 <=> k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_3),
% 0.22/0.55    inference(resolution,[],[f98,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | sK0 = X3) ) | ~spl7_3),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | sK0 = X3 | sK0 = X3 | sK0 = X3) ) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f73,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl7_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f85])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.55    inference(equality_resolution,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.55    inference(definition_unfolding,[],[f44,f39])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.55  % (4940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ~spl7_4 | ~spl7_1 | ~spl7_7 | ~spl7_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f126,f120,f128,f75,f100])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    spl7_6 <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_6),
% 0.22/0.55    inference(superposition,[],[f36,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f120])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ~spl7_1 | spl7_6 | ~spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f117,f85,f120,f75])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl7_3),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f26,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2] : (k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1)) | ~v1_relat_1(X2)) ) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f52,f87])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f27,f49])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ~spl7_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f50,f107])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.55    inference(definition_unfolding,[],[f24,f49])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.55    inference(negated_conjecture,[],[f10])).
% 0.22/0.55  fof(f10,conjecture,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl7_4 | ~spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f97,f85,f100])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f68,f87])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 0.22/0.55    inference(equality_resolution,[],[f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 0.22/0.55    inference(equality_resolution,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.55    inference(definition_unfolding,[],[f47,f39])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f51,f85])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.55    inference(definition_unfolding,[],[f23,f49])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f22,f80])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    v1_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f21,f75])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    v1_relat_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (4946)------------------------------
% 0.22/0.55  % (4946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4946)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (4946)Memory used [KB]: 10874
% 0.22/0.55  % (4946)Time elapsed: 0.130 s
% 0.22/0.55  % (4946)------------------------------
% 0.22/0.55  % (4946)------------------------------
% 0.22/0.55  % (4933)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (4923)Success in time 0.186 s
%------------------------------------------------------------------------------
