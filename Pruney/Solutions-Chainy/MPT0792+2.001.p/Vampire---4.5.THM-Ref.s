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
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 423 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f112,f139,f156,f169,f183])).

% (28738)Termination reason: Refutation not found, incomplete strategy

% (28738)Memory used [KB]: 1663
% (28738)Time elapsed: 0.061 s
% (28738)------------------------------
% (28738)------------------------------
% (28751)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f183,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_16 ),
    inference(unit_resulting_resolution,[],[f75,f70,f65,f65,f50,f168,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v2_wellord1(X2)
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f168,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_16
  <=> r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f70,plain,
    ( v2_wellord1(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_4
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f169,plain,
    ( ~ spl6_16
    | spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f158,f109,f53,f166])).

fof(f53,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f109,plain,
    ( spl6_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f158,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | spl6_1
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f55,f111])).

fof(f111,plain,
    ( sK0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f55,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f156,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_13 ),
    inference(avatar_split_clause,[],[f144,f135,f73,f68])).

fof(f135,plain,
    ( spl6_13
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f144,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_wellord1(sK2)
    | spl6_13 ),
    inference(resolution,[],[f137,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f137,plain,
    ( ~ v6_relat_2(sK2)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f139,plain,
    ( ~ spl6_13
    | ~ spl6_5
    | spl6_1
    | spl6_10
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9 ),
    inference(avatar_split_clause,[],[f132,f105,f63,f58,f109,f53,f73,f135])).

fof(f58,plain,
    ( spl6_2
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f105,plain,
    ( spl6_9
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f132,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v6_relat_2(sK2)
    | spl6_9 ),
    inference(resolution,[],[f22,f107])).

fof(f107,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f112,plain,
    ( ~ spl6_5
    | ~ spl6_9
    | spl6_10
    | spl6_6 ),
    inference(avatar_split_clause,[],[f103,f78,f109,f105,f73])).

fof(f78,plain,
    ( spl6_6
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f103,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | spl6_6 ),
    inference(resolution,[],[f46,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_wellord1(X0,X1))
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f81,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | sK1 != X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(f76,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f17,f73])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f18,f68])).

fof(f18,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f19,f63])).

fof(f19,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f20,f58])).

fof(f20,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28754)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (28746)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (28732)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28736)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (28738)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (28735)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28733)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (28738)Refutation not found, incomplete strategy% (28738)------------------------------
% 0.21/0.51  % (28738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28741)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (28746)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f112,f139,f156,f169,f183])).
% 0.21/0.52  % (28738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28738)Memory used [KB]: 1663
% 0.21/0.52  % (28738)Time elapsed: 0.061 s
% 0.21/0.52  % (28738)------------------------------
% 0.21/0.52  % (28738)------------------------------
% 0.21/0.52  % (28751)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    $false | (~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f75,f70,f65,f65,f50,f168,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~v2_wellord1(X2) | ~r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK0),sK2) | spl6_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl6_16 <=> r2_hidden(k4_tarski(sK0,sK0),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl6_3 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    v2_wellord1(sK2) | ~spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl6_4 <=> v2_wellord1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl6_5 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~spl6_16 | spl6_1 | ~spl6_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f158,f109,f53,f166])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl6_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl6_10 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK0),sK2) | (spl6_1 | ~spl6_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f55,f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~spl6_4 | ~spl6_5 | spl6_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f144,f135,f73,f68])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl6_13 <=> v6_relat_2(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | ~v2_wellord1(sK2) | spl6_13),
% 0.21/0.52    inference(resolution,[],[f137,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (v6_relat_2(X0) | ~v1_relat_1(X0) | ~v2_wellord1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~v6_relat_2(sK2) | spl6_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~spl6_13 | ~spl6_5 | spl6_1 | spl6_10 | ~spl6_2 | ~spl6_3 | spl6_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f132,f105,f63,f58,f109,f53,f73,f135])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl6_2 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl6_9 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_relat_1(sK2) | ~v6_relat_2(sK2) | spl6_9),
% 0.21/0.52    inference(resolution,[],[f22,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK1,sK0),sK2) | spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~spl6_5 | ~spl6_9 | spl6_10 | spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f103,f78,f109,f105,f73])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl6_6 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2) | ~v1_relat_1(sK2) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f46,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_wellord1(X0,X1)) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f78])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.21/0.52    inference(equality_resolution,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k1_wellord1(sK2,sK0)) | sK1 != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(k4_tarski(X0,X1),X2) & (! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f73])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f68])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    v2_wellord1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f63])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f58])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28746)------------------------------
% 0.21/0.52  % (28746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28746)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28746)Memory used [KB]: 6268
% 0.21/0.52  % (28746)Time elapsed: 0.063 s
% 0.21/0.52  % (28746)------------------------------
% 0.21/0.52  % (28746)------------------------------
% 0.21/0.52  % (28730)Success in time 0.156 s
%------------------------------------------------------------------------------
