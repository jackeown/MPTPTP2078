%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 115 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  188 ( 370 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f44,f48,f52,f63,f68,f74,f80,f87,f94])).

fof(f94,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f88,f85,f33,f23])).

fof(f23,plain,
    ( spl4_1
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f33,plain,
    ( spl4_3
  <=> r1_tarski(k3_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_tarski(k3_tarski(X0),sK1)
        | ~ r2_hidden(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f88,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f86,f35])).

fof(f35,plain,
    ( r1_tarski(k3_tarski(sK0),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_tarski(X0),sK1)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f81,f78,f38,f85])).

fof(f38,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f78,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_tarski(X0),sK1)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl4_2
    | spl4_12
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f75,f72,f42,f78,f28])).

fof(f28,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f42,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK3(sK2,sK1),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,sK1) )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f73,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK2,sK1),X1)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl4_11
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f70,f66,f50,f72])).

fof(f50,plain,
    ( spl4_7
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f66,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK3(sK2,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK3(sK2,sK1),X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl4_10
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f64,f61,f28,f66])).

fof(f61,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK3(sK2,sK1),X0) )
    | spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f62,f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X1)
        | ~ r2_hidden(sK3(X0,X1),X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl4_9
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f59,f50,f46,f61])).

fof(f46,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(sK2,sK1)
    & r2_hidden(sK2,sK0)
    & r1_tarski(k3_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK2,sK1)
      & r2_hidden(sK2,sK0)
      & r1_tarski(k3_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f31,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (18587)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.44  % (18587)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f44,f48,f52,f63,f68,f74,f80,f87,f94])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    ~spl4_1 | ~spl4_3 | ~spl4_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f88,f85,f33,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    spl4_1 <=> r2_hidden(sK2,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    spl4_3 <=> r1_tarski(k3_tarski(sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    spl4_13 <=> ! [X0] : (~r1_tarski(k3_tarski(X0),sK1) | ~r2_hidden(sK2,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    ~r2_hidden(sK2,sK0) | (~spl4_3 | ~spl4_13)),
% 0.22/0.44    inference(resolution,[],[f86,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    r1_tarski(k3_tarski(sK0),sK1) | ~spl4_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f33])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(k3_tarski(X0),sK1) | ~r2_hidden(sK2,X0)) ) | ~spl4_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f85])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    spl4_13 | ~spl4_4 | ~spl4_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f81,f78,f38,f85])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl4_4 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl4_12 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK2,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(k3_tarski(X0),sK1) | ~r2_hidden(sK2,X0)) ) | (~spl4_4 | ~spl4_12)),
% 0.22/0.44    inference(resolution,[],[f79,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl4_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,sK1)) ) | ~spl4_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl4_2 | spl4_12 | ~spl4_5 | ~spl4_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f72,f42,f78,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    spl4_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl4_5 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl4_11 <=> ! [X1,X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK3(sK2,sK1),X1) | ~r1_tarski(X1,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,sK1)) ) | (~spl4_5 | ~spl4_11)),
% 0.22/0.44    inference(resolution,[],[f73,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) ) | ~spl4_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(sK3(sK2,sK1),X1) | ~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0)) ) | ~spl4_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl4_11 | ~spl4_7 | ~spl4_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f70,f66,f50,f72])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl4_7 <=> ! [X1,X3,X0] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl4_10 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK3(sK2,sK1),X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK3(sK2,sK1),X1) | ~r1_tarski(X1,X0)) ) | (~spl4_7 | ~spl4_10)),
% 0.22/0.44    inference(resolution,[],[f67,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) ) | ~spl4_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(sK3(sK2,sK1),X0) | ~r1_tarski(X0,sK1)) ) | ~spl4_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl4_10 | spl4_2 | ~spl4_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f64,f61,f28,f66])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl4_9 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK3(sK2,sK1),X0)) ) | (spl4_2 | ~spl4_9)),
% 0.22/0.44    inference(resolution,[],[f62,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ~r1_tarski(sK2,sK1) | spl4_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f28])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK3(X0,X1),X2)) ) | ~spl4_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl4_9 | ~spl4_6 | ~spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f59,f50,f46,f61])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl4_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) ) | (~spl4_6 | ~spl4_7)),
% 0.22/0.44    inference(resolution,[],[f51,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) ) | ~spl4_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f46])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f50])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(rectify,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl4_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f46])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl4_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl4_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f38])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl4_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f33])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    r1_tarski(k3_tarski(sK0),sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => (~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.44    inference(flattening,[],[f5])).
% 0.22/0.44  fof(f5,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & (r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.22/0.44    inference(negated_conjecture,[],[f3])).
% 0.22/0.44  fof(f3,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ~spl4_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f28])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~r1_tarski(sK2,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl4_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f23])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    r2_hidden(sK2,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (18587)------------------------------
% 0.22/0.44  % (18587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (18587)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (18587)Memory used [KB]: 5373
% 0.22/0.44  % (18587)Time elapsed: 0.029 s
% 0.22/0.44  % (18587)------------------------------
% 0.22/0.44  % (18587)------------------------------
% 0.22/0.44  % (18570)Success in time 0.078 s
%------------------------------------------------------------------------------
