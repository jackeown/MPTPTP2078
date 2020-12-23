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
% DateTime   : Thu Dec  3 12:50:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 216 expanded)
%              Number of equality atoms :   48 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f45,f54,f66,f67])).

fof(f67,plain,
    ( sK0 != k3_xboole_0(sK0,k2_relat_1(sK1))
    | k1_xboole_0 != k3_xboole_0(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f66,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f59,f52,f61])).

fof(f61,plain,
    ( spl2_7
  <=> k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f52,plain,
    ( spl2_6
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f59,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f19,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f50,f38,f26,f52])).

fof(f26,plain,
    ( spl2_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f50,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f27])).

fof(f27,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f48,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f47,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f47,plain,
    ( ! [X0] :
        ( r1_xboole_0(k2_relat_1(sK1),X0)
        | k1_xboole_0 != k10_relat_1(sK1,X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f20,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f45,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f41,f30,f43])).

fof(f43,plain,
    ( spl2_5
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f30,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f36,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f34,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f26])).

fof(f18,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (26431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (26431)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f45,f54,f66,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    sK0 != k3_xboole_0(sK0,k2_relat_1(sK1)) | k1_xboole_0 != k3_xboole_0(sK0,k2_relat_1(sK1)) | k1_xboole_0 = sK0),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl2_7 | ~spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f59,f52,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl2_7 <=> k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl2_6 <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_6),
% 0.21/0.46    inference(superposition,[],[f19,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl2_6 | ~spl2_1 | ~spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f38,f26,f52])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    spl2_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl2_4 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_4)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_4)),
% 0.21/0.46    inference(superposition,[],[f48,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f26])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_4),
% 0.21/0.46    inference(resolution,[],[f47,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0] : (r1_xboole_0(k2_relat_1(sK1),X0) | k1_xboole_0 != k10_relat_1(sK1,X0)) ) | ~spl2_4),
% 0.21/0.46    inference(resolution,[],[f20,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl2_5 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f30,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl2_5 <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl2_2 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.46    inference(resolution,[],[f22,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f30])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f38])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl2_3 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f26])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (26431)------------------------------
% 0.21/0.46  % (26431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26431)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (26431)Memory used [KB]: 10618
% 0.21/0.46  % (26431)Time elapsed: 0.058 s
% 0.21/0.46  % (26431)------------------------------
% 0.21/0.46  % (26431)------------------------------
% 0.21/0.46  % (26424)Success in time 0.102 s
%------------------------------------------------------------------------------
