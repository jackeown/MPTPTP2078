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
% DateTime   : Thu Dec  3 12:45:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  63 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 149 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f54,f59,f66,f90,f102])).

fof(f102,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f89,f24])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f90,plain,
    ( ~ spl2_9
    | spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f78,f63,f51,f87])).

fof(f51,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f78,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f53,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f53,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f66,plain,
    ( ~ spl2_4
    | spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f60,f39,f63,f56])).

fof(f56,plain,
    ( spl2_4
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f39,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1)
    | spl2_1 ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f41,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f59,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f49,f44,f56,f51])).

fof(f44,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( m1_subset_1(sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,
    ( ~ spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f48,f44,f51])).

fof(f48,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n016.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:21:04 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.42  % (29184)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % (29184)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f42,f47,f54,f59,f66,f90,f102])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    $false | spl2_9),
% 0.21/0.43    inference(resolution,[],[f89,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | spl2_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl2_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    ~spl2_9 | spl2_3 | ~spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f78,f63,f51,f87])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl2_3 <=> v1_xboole_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl2_5 <=> k1_xboole_0 = sK1),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | (spl2_3 | ~spl2_5)),
% 0.21/0.43    inference(backward_demodulation,[],[f53,f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    k1_xboole_0 = sK1 | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ~v1_xboole_0(sK1) | spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ~spl2_4 | spl2_5 | spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f60,f39,f63,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl2_4 <=> m1_subset_1(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl2_1 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1) | spl2_1),
% 0.21/0.43    inference(resolution,[],[f41,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl2_3 | spl2_4 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f49,f44,f56,f51])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    m1_subset_1(sK0,sK1) | v1_xboole_0(sK1) | ~spl2_2),
% 0.21/0.43    inference(resolution,[],[f46,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ~spl2_3 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f48,f44,f51])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ~v1_xboole_0(sK1) | ~spl2_2),
% 0.21/0.43    inference(resolution,[],[f46,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f12])).
% 0.21/0.43  fof(f12,conjecture,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (29184)------------------------------
% 0.21/0.43  % (29184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (29184)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (29184)Memory used [KB]: 10618
% 0.21/0.43  % (29184)Time elapsed: 0.005 s
% 0.21/0.43  % (29184)------------------------------
% 0.21/0.43  % (29184)------------------------------
% 0.21/0.43  % (29172)Success in time 0.056 s
%------------------------------------------------------------------------------
