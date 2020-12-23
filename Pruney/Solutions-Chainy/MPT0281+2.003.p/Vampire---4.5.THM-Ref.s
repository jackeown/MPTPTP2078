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
% DateTime   : Thu Dec  3 12:41:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 223 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  361 ( 957 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f753,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f99,f353,f382,f447,f450,f465,f470,f528,f602,f670,f739,f747,f752])).

fof(f752,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f86,f178,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f178,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f747,plain,
    ( spl4_1
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | spl4_1
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f86,f263,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f263,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl4_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f739,plain,
    ( spl4_9
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f737])).

fof(f737,plain,
    ( $false
    | spl4_9
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f179,f726])).

fof(f726,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_28 ),
    inference(superposition,[],[f60,f601])).

fof(f601,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl4_28
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f179,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f670,plain,
    ( ~ spl4_2
    | ~ spl4_15
    | spl4_22
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_15
    | spl4_22
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f441,f446,f656])).

fof(f656,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK1))
        | r2_hidden(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(superposition,[],[f193,f289])).

fof(f289,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl4_15
  <=> k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f193,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
        | ~ r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f80,f91])).

fof(f91,plain,
    ( k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_2
  <=> k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

% (26096)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f446,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl4_23
  <=> r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f441,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl4_22
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f602,plain,
    ( ~ spl4_23
    | spl4_28
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f574,f525,f89,f599,f444])).

fof(f525,plain,
    ( spl4_26
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f574,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(resolution,[],[f527,f274])).

fof(f274,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_xboole_0(sK0,sK1),X6)
        | k2_xboole_0(sK0,sK1) = X6
        | ~ r2_hidden(X6,k1_zfmisc_1(sK1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f193,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

% (26102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f527,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f525])).

fof(f528,plain,
    ( spl4_26
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f474,f462,f525])).

fof(f462,plain,
    ( spl4_25
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f474,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl4_25 ),
    inference(resolution,[],[f464,f79])).

fof(f464,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f462])).

fof(f470,plain,
    ( spl4_19
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl4_19
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f381,f460,f79])).

fof(f460,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f458])).

% (26100)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f458,plain,
    ( spl4_24
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f381,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl4_19
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f465,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f422,f89,f462,f458])).

fof(f422,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f415,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f415,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_xboole_0(sK0,sK1))
        | r2_hidden(X2,k1_zfmisc_1(sK1))
        | r2_hidden(X2,k1_zfmisc_1(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f403,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
        | r2_hidden(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f82,f91])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f450,plain,
    ( spl4_12
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl4_12
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f264,f442,f79])).

fof(f442,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f440])).

fof(f264,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f447,plain,
    ( spl4_22
    | spl4_23
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f421,f89,f444,f440])).

fof(f421,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK1))
    | r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f415,f116])).

fof(f116,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f382,plain,
    ( ~ spl4_19
    | spl4_18 ),
    inference(avatar_split_clause,[],[f354,f350,f379])).

fof(f350,plain,
    ( spl4_18
  <=> r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f354,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | spl4_18 ),
    inference(resolution,[],[f352,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

% (26083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f352,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f350])).

fof(f353,plain,
    ( ~ spl4_18
    | spl4_15
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f275,f96,f287,f350])).

fof(f96,plain,
    ( spl4_3
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f275,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))
    | ~ r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f50,f98])).

fof(f98,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f93,f89,f96])).

fof(f93,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(superposition,[],[f60,f91])).

fof(f92,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f87,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:38:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26097)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (26089)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (26080)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (26078)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (26079)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26088)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (26073)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (26091)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (26077)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (26075)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (26076)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (26074)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (26074)Refutation not found, incomplete strategy% (26074)------------------------------
% 0.22/0.54  % (26074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26074)Memory used [KB]: 1663
% 0.22/0.54  % (26074)Time elapsed: 0.116 s
% 0.22/0.54  % (26074)------------------------------
% 0.22/0.54  % (26074)------------------------------
% 0.22/0.54  % (26087)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (26097)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f753,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f87,f92,f99,f353,f382,f447,f450,f465,f470,f528,f602,f670,f739,f747,f752])).
% 0.22/0.54  fof(f752,plain,(
% 0.22/0.54    spl4_1 | ~spl4_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f748])).
% 0.22/0.54  fof(f748,plain,(
% 0.22/0.54    $false | (spl4_1 | ~spl4_9)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f86,f178,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r3_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl4_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl4_9 <=> r1_tarski(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~r3_xboole_0(sK0,sK1) | spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl4_1 <=> r3_xboole_0(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f747,plain,(
% 0.22/0.54    spl4_1 | ~spl4_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f743])).
% 0.22/0.54  fof(f743,plain,(
% 0.22/0.54    $false | (spl4_1 | ~spl4_12)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f86,f263,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r3_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | ~spl4_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f262])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    spl4_12 <=> r1_tarski(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.54  fof(f739,plain,(
% 0.22/0.54    spl4_9 | ~spl4_28),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f737])).
% 0.22/0.54  fof(f737,plain,(
% 0.22/0.54    $false | (spl4_9 | ~spl4_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f726])).
% 0.22/0.54  fof(f726,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl4_28),
% 0.22/0.54    inference(superposition,[],[f60,f601])).
% 0.22/0.54  fof(f601,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK0,sK1) | ~spl4_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f599])).
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    spl4_28 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1) | spl4_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f670,plain,(
% 0.22/0.54    ~spl4_2 | ~spl4_15 | spl4_22 | ~spl4_23),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f666])).
% 0.22/0.54  fof(f666,plain,(
% 0.22/0.54    $false | (~spl4_2 | ~spl4_15 | spl4_22 | ~spl4_23)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f441,f446,f656])).
% 0.22/0.54  fof(f656,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK1)) | r2_hidden(X0,k1_zfmisc_1(sK0))) ) | (~spl4_2 | ~spl4_15)),
% 0.22/0.54    inference(superposition,[],[f193,f289])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) | ~spl4_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f287])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    spl4_15 <=> k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl4_2),
% 0.22/0.54    inference(superposition,[],[f80,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl4_2 <=> k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f37])).
% 0.22/0.54  % (26096)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~spl4_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f444])).
% 0.22/0.54  fof(f444,plain,(
% 0.22/0.54    spl4_23 <=> r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.54  fof(f441,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl4_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f440])).
% 0.22/0.54  fof(f440,plain,(
% 0.22/0.54    spl4_22 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.54  fof(f602,plain,(
% 0.22/0.54    ~spl4_23 | spl4_28 | ~spl4_2 | ~spl4_26),
% 0.22/0.54    inference(avatar_split_clause,[],[f574,f525,f89,f599,f444])).
% 0.22/0.54  fof(f525,plain,(
% 0.22/0.54    spl4_26 <=> r1_tarski(k2_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.54  fof(f574,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK0,sK1) | ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | (~spl4_2 | ~spl4_26)),
% 0.22/0.54    inference(resolution,[],[f527,f274])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    ( ! [X6] : (~r1_tarski(k2_xboole_0(sK0,sK1),X6) | k2_xboole_0(sK0,sK1) = X6 | ~r2_hidden(X6,k1_zfmisc_1(sK1))) ) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f50,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK0,sK1)) | ~r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f193,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f17])).
% 0.22/0.54  % (26102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f527,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK0,sK1),sK1) | ~spl4_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f525])).
% 0.22/0.54  fof(f528,plain,(
% 0.22/0.54    spl4_26 | ~spl4_25),
% 0.22/0.54    inference(avatar_split_clause,[],[f474,f462,f525])).
% 0.22/0.54  fof(f462,plain,(
% 0.22/0.54    spl4_25 <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.54  fof(f474,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK0,sK1),sK1) | ~spl4_25),
% 0.22/0.54    inference(resolution,[],[f464,f79])).
% 0.22/0.54  fof(f464,plain,(
% 0.22/0.54    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl4_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f462])).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    spl4_19 | ~spl4_24),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f466])).
% 0.22/0.54  fof(f466,plain,(
% 0.22/0.54    $false | (spl4_19 | ~spl4_24)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f381,f460,f79])).
% 0.22/0.54  fof(f460,plain,(
% 0.22/0.54    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f458])).
% 0.22/0.54  % (26100)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  fof(f458,plain,(
% 0.22/0.54    spl4_24 <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.54  fof(f381,plain,(
% 0.22/0.54    ~r1_tarski(k2_xboole_0(sK0,sK1),sK0) | spl4_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f379])).
% 0.22/0.54  fof(f379,plain,(
% 0.22/0.54    spl4_19 <=> r1_tarski(k2_xboole_0(sK0,sK1),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.54  fof(f465,plain,(
% 0.22/0.54    spl4_24 | spl4_25 | ~spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f422,f89,f462,f458])).
% 0.22/0.54  fof(f422,plain,(
% 0.22/0.54    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f415,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f415,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(X2,k2_xboole_0(sK0,sK1)) | r2_hidden(X2,k1_zfmisc_1(sK1)) | r2_hidden(X2,k1_zfmisc_1(sK0))) ) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f403,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f403,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | r2_hidden(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl4_2),
% 0.22/0.55    inference(superposition,[],[f82,f91])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f450,plain,(
% 0.22/0.55    spl4_12 | ~spl4_22),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f448])).
% 0.22/0.55  fof(f448,plain,(
% 0.22/0.55    $false | (spl4_12 | ~spl4_22)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f264,f442,f79])).
% 0.22/0.55  fof(f442,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f440])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK0) | spl4_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f262])).
% 0.22/0.55  fof(f447,plain,(
% 0.22/0.55    spl4_22 | spl4_23 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f421,f89,f444,f440])).
% 0.22/0.55  fof(f421,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_zfmisc_1(sK1)) | r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.55    inference(resolution,[],[f415,f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.55    inference(superposition,[],[f60,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.55  fof(f382,plain,(
% 0.22/0.55    ~spl4_19 | spl4_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f354,f350,f379])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    spl4_18 <=> r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.55  fof(f354,plain,(
% 0.22/0.55    ~r1_tarski(k2_xboole_0(sK0,sK1),sK0) | spl4_18),
% 0.22/0.55    inference(resolution,[],[f352,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.22/0.55  % (26083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  fof(f352,plain,(
% 0.22/0.55    ~r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | spl4_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f350])).
% 0.22/0.55  fof(f353,plain,(
% 0.22/0.55    ~spl4_18 | spl4_15 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f275,f96,f287,f350])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    spl4_3 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.55  fof(f275,plain,(
% 0.22/0.55    k1_zfmisc_1(sK0) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) | ~r1_tarski(k1_zfmisc_1(k2_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.22/0.55    inference(resolution,[],[f50,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~spl4_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f96])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl4_3 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f93,f89,f96])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~spl4_2),
% 0.22/0.55    inference(superposition,[],[f60,f91])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f41,f89])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))) => (~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f19])).
% 0.22/0.55  fof(f19,conjecture,(
% 0.22/0.55    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f42,f84])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ~r3_xboole_0(sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (26097)------------------------------
% 0.22/0.55  % (26097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26097)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (26097)Memory used [KB]: 11129
% 0.22/0.55  % (26097)Time elapsed: 0.075 s
% 0.22/0.55  % (26097)------------------------------
% 0.22/0.55  % (26097)------------------------------
% 0.22/0.55  % (26093)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (26103)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (26103)Refutation not found, incomplete strategy% (26103)------------------------------
% 0.22/0.55  % (26103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26103)Memory used [KB]: 1663
% 0.22/0.55  % (26103)Time elapsed: 0.129 s
% 0.22/0.55  % (26103)------------------------------
% 0.22/0.55  % (26103)------------------------------
% 0.22/0.55  % (26072)Success in time 0.183 s
%------------------------------------------------------------------------------
