%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 275 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f45,f50,f56,f64,f71,f74,f75,f77,f80])).

fof(f80,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f79,f41,f68,f47])).

fof(f47,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f68,plain,
    ( spl2_6
  <=> r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f41,plain,
    ( spl2_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f28,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f77,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f73,f68,f61])).

fof(f61,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f73,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f70,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f61,f37])).

fof(f37,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(resolution,[],[f63,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f63,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f74,plain,
    ( ~ spl2_3
    | spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f72,f68,f41,f47])).

fof(f72,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f66,f61,f68])).

fof(f66,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f63,f30])).

fof(f64,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f58,f53,f61])).

fof(f53,plain,
    ( spl2_4
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f58,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | ~ spl2_4 ),
    inference(superposition,[],[f26,f55])).

fof(f55,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f56,plain,
    ( spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f51,f37,f53])).

fof(f51,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | spl2_1 ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f39,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f45,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f23,f41,f37])).

fof(f23,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f24,f41,f37])).

fof(f24,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (2829)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.41  % (2829)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f44,f45,f50,f56,f64,f71,f74,f75,f77,f80])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    ~spl2_3 | spl2_6 | ~spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f79,f41,f68,f47])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    spl2_6 <=> r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl2_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.41    inference(superposition,[],[f28,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f41])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(nnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    spl2_5 | ~spl2_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f73,f68,f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    spl2_5 <=> r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | ~spl2_6),
% 0.21/0.41    inference(resolution,[],[f70,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ~spl2_1 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f65,f61,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 0.21/0.42    inference(resolution,[],[f63,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ~spl2_3 | spl2_2 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f72,f68,f41,f47])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_6),
% 0.21/0.42    inference(resolution,[],[f70,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl2_6 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f66,f61,f68])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl2_5),
% 0.21/0.42    inference(resolution,[],[f63,f30])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl2_5 | ~spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f58,f53,f61])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_4 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | ~spl2_4),
% 0.21/0.42    inference(superposition,[],[f26,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_4 | spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f51,f37,f53])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | spl2_1),
% 0.21/0.42    inference(resolution,[],[f39,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f10])).
% 0.21/0.42  fof(f10,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl2_1 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f41,f37])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ~spl2_1 | spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f41,f37])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2829)------------------------------
% 0.21/0.42  % (2829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2829)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2829)Memory used [KB]: 10618
% 0.21/0.42  % (2829)Time elapsed: 0.006 s
% 0.21/0.42  % (2829)------------------------------
% 0.21/0.42  % (2829)------------------------------
% 0.21/0.42  % (2817)Success in time 0.063 s
%------------------------------------------------------------------------------
