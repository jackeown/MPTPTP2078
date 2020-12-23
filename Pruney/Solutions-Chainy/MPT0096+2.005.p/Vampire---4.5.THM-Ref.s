%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  75 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :  126 ( 176 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f47,f51,f94,f139,f225,f237,f243])).

fof(f243,plain,
    ( ~ spl2_1
    | spl2_36 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl2_1
    | spl2_36 ),
    inference(resolution,[],[f236,f23])).

fof(f23,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_1
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f236,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1)
    | spl2_36 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl2_36
  <=> r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f237,plain,
    ( ~ spl2_36
    | spl2_2
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f228,f223,f26,f234])).

fof(f26,plain,
    ( spl2_2
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f223,plain,
    ( spl2_35
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)
        | r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f228,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1)
    | spl2_2
    | ~ spl2_35 ),
    inference(resolution,[],[f224,f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) )
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl2_35
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f146,f137,f49,f223])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f137,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)
        | r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)
        | r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) )
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(resolution,[],[f138,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2))
        | ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f101,f92,f31,f137])).

fof(f31,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X3,X5,X2,X4] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)
        | r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) )
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f93,f32])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f93,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f53,f45,f35,f92])).

fof(f35,plain,
    ( spl2_4
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f53,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5)) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f46,f36])).

fof(f36,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f46,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f51,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f37,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f29,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f22])).

fof(f16,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (15636)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.43  % (15636)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f244,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f47,f51,f94,f139,f225,f237,f243])).
% 0.20/0.43  fof(f243,plain,(
% 0.20/0.43    ~spl2_1 | spl2_36),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f242])).
% 0.20/0.43  fof(f242,plain,(
% 0.20/0.43    $false | (~spl2_1 | spl2_36)),
% 0.20/0.43    inference(resolution,[],[f236,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    spl2_1 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f236,plain,(
% 0.20/0.43    ~r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1) | spl2_36),
% 0.20/0.43    inference(avatar_component_clause,[],[f234])).
% 0.20/0.43  fof(f234,plain,(
% 0.20/0.43    spl2_36 <=> r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.43  fof(f237,plain,(
% 0.20/0.43    ~spl2_36 | spl2_2 | ~spl2_35),
% 0.20/0.43    inference(avatar_split_clause,[],[f228,f223,f26,f234])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    spl2_2 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f223,plain,(
% 0.20/0.43    spl2_35 <=> ! [X1,X0,X2] : (~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    ~r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK1),sK1) | (spl2_2 | ~spl2_35)),
% 0.20/0.43    inference(resolution,[],[f224,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f26])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) | ~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)) ) | ~spl2_35),
% 0.20/0.43    inference(avatar_component_clause,[],[f223])).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    spl2_35 | ~spl2_7 | ~spl2_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f146,f137,f49,f223])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    spl2_21 <=> ! [X1,X0,X2] : (~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) | r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ) | (~spl2_7 | ~spl2_21)),
% 0.20/0.43    inference(resolution,[],[f138,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) | ~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1)) ) | ~spl2_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f137])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    spl2_21 | ~spl2_3 | ~spl2_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f101,f92,f31,f137])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    spl2_3 <=> ! [X1,X0] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl2_14 <=> ! [X3,X5,X2,X4] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),X1) | r1_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2))) ) | (~spl2_3 | ~spl2_14)),
% 0.20/0.43    inference(resolution,[],[f93,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f31])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ( ! [X4,X2,X5,X3] : (r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5)) | ~r1_xboole_0(X2,X3)) ) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f92])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl2_14 | ~spl2_4 | ~spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f53,f45,f35,f92])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl2_4 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X4,X2,X5,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(k3_xboole_0(X4,X3),X5))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.43    inference(resolution,[],[f46,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,X2))) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f45])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f49])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f45])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f35])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f31])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f16,f22])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (15636)------------------------------
% 0.20/0.43  % (15636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (15636)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (15636)Memory used [KB]: 5500
% 0.20/0.43  % (15636)Time elapsed: 0.033 s
% 0.20/0.43  % (15636)------------------------------
% 0.20/0.43  % (15636)------------------------------
% 0.20/0.43  % (15619)Success in time 0.083 s
%------------------------------------------------------------------------------
