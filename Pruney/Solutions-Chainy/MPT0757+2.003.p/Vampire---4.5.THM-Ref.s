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
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 313 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7950)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f71,f82,f87,f92,f119])).

fof(f119,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_8
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f117,f91])).

fof(f91,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f117,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_8 ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f36,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl3_2
    | spl3_8 ),
    inference(resolution,[],[f113,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_8
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f113,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ v3_ordinal1(X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK0)
        | r1_tarski(sK0,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f62])).

fof(f62,plain,
    ( ! [X1] :
        ( ~ r1_ordinal1(sK0,X1)
        | r1_tarski(sK0,X1)
        | ~ v3_ordinal1(X1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f41,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( ! [X2] :
        ( r1_ordinal1(sK0,X2)
        | ~ v3_ordinal1(X2)
        | r2_hidden(X2,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f92,plain,
    ( ~ spl3_9
    | spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f83,f49,f44,f89])).

fof(f44,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f64,f51])).

fof(f51,plain,
    ( sK0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f64,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f46,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f87,plain,
    ( ~ spl3_2
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl3_2
    | spl3_7 ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f85,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_7 ),
    inference(resolution,[],[f77,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f77,plain,
    ( ~ v1_ordinal1(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_7
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f82,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f73,f68,f79,f75])).

fof(f68,plain,
    ( spl3_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f73,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v1_ordinal1(sK0)
    | spl3_6 ),
    inference(resolution,[],[f70,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f70,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( ~ spl3_6
    | spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f66,f54,f49,f68])).

fof(f54,plain,
    ( spl3_5
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f65,f51])).

fof(f65,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | spl3_5 ),
    inference(resolution,[],[f56,f31])).

fof(f56,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f52,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (7960)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (7946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (7949)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (7949)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  % (7950)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f71,f82,f87,f92,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2 | spl3_8 | spl3_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_2 | spl3_8 | spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl3_9 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | (~spl3_1 | ~spl3_2 | spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v3_ordinal1(sK1) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1 <=> v3_ordinal1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | (~spl3_2 | spl3_8)),
% 0.21/0.48    inference(resolution,[],[f113,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_8 <=> r2_hidden(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | r1_tarski(sK0,X0)) ) | ~spl3_2),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | r1_tarski(sK0,X0) | ~v3_ordinal1(X0)) ) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f63,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_ordinal1(sK0,X1) | r1_tarski(sK0,X1) | ~v3_ordinal1(X1)) ) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f41,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v3_ordinal1(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_2 <=> v3_ordinal1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2] : (r1_ordinal1(sK0,X2) | ~v3_ordinal1(X2) | r2_hidden(X2,sK0)) ) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f41,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~spl3_9 | spl3_3 | spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f83,f49,f44,f89])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_4 <=> sK0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | (spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sK0 != sK1 | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK0 = sK1 | ~r1_tarski(sK0,sK1) | spl3_3),
% 0.21/0.48    inference(resolution,[],[f46,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK1) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~spl3_2 | spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    $false | (~spl3_2 | spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f41])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v3_ordinal1(sK0) | spl3_7),
% 0.21/0.48    inference(resolution,[],[f77,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~v1_ordinal1(sK0) | spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_7 <=> v1_ordinal1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~spl3_7 | ~spl3_8 | spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f68,f79,f75])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_6 <=> r1_tarski(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | ~v1_ordinal1(sK0) | spl3_6),
% 0.21/0.48    inference(resolution,[],[f70,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~spl3_6 | spl3_4 | spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f54,f49,f68])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_5 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0) | (spl3_4 | spl3_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f51])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    sK0 = sK1 | ~r1_tarski(sK1,sK0) | spl3_5),
% 0.21/0.48    inference(resolution,[],[f56,f31])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~r2_xboole_0(sK1,sK0) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r2_xboole_0(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f49])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    sK0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f44])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v3_ordinal1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v3_ordinal1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7949)------------------------------
% 0.21/0.48  % (7949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7949)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7949)Memory used [KB]: 10618
% 0.21/0.48  % (7949)Time elapsed: 0.063 s
% 0.21/0.48  % (7949)------------------------------
% 0.21/0.48  % (7949)------------------------------
% 0.21/0.48  % (7952)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (7959)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (7943)Success in time 0.12 s
%------------------------------------------------------------------------------
