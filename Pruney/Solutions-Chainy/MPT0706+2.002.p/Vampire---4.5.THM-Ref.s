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
% DateTime   : Thu Dec  3 12:54:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 108 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 398 expanded)
%              Number of equality atoms :   43 ( 129 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f46,f52,f59,f65,f73,f84])).

fof(f84,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f80,f70,f24,f32])).

fof(f32,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f24,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f70,plain,
    ( spl3_10
  <=> sK1 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f80,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_10 ),
    inference(superposition,[],[f21,f71])).

fof(f71,plain,
    ( sK1 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,
    ( ~ spl3_2
    | spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f67,f63,f70,f28])).

fof(f28,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_9
  <=> k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f67,plain,
    ( sK1 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f21,f64])).

fof(f64,plain,
    ( k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f61,f57,f36,f63])).

fof(f36,plain,
    ( spl3_4
  <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f61,plain,
    ( k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f58,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,
    ( k3_xboole_0(sK1,k2_relat_1(sK2)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f58,f37])).

fof(f37,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f59,plain,
    ( ~ spl3_6
    | spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f53,f50,f57,f44])).

fof(f44,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f53,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(superposition,[],[f51,f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f51,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f47,f40,f50,f44])).

fof(f40,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5 ),
    inference(resolution,[],[f22,f41])).

fof(f41,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f14,f44])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & r1_tarski(sK1,k2_relat_1(sK2))
    & r1_tarski(sK0,k2_relat_1(sK2))
    & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK0 != sK1
      & r1_tarski(sK1,k2_relat_1(sK2))
      & r1_tarski(sK0,k2_relat_1(sK2))
      & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f24])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (13785)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (13777)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (13777)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f46,f52,f59,f65,f73,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~spl3_3 | spl3_1 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f80,f70,f24,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    spl3_1 <=> sK0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_10 <=> sK1 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    sK0 = sK1 | ~r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_10),
% 0.21/0.47    inference(superposition,[],[f21,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    sK1 = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~spl3_2 | spl3_10 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f67,f63,f70,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_9 <=> k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    sK1 = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~spl3_9),
% 0.21/0.47    inference(superposition,[],[f21,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_9 | ~spl3_4 | ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f57,f36,f63])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl3_4 <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl3_8 <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k3_xboole_0(sK1,k2_relat_1(sK2)) = k3_xboole_0(sK0,k2_relat_1(sK2)) | (~spl3_4 | ~spl3_8)),
% 0.21/0.47    inference(forward_demodulation,[],[f60,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) ) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k3_xboole_0(sK1,k2_relat_1(sK2)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl3_4 | ~spl3_8)),
% 0.21/0.47    inference(superposition,[],[f58,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~spl3_6 | spl3_8 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f50,f57,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_7 <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.21/0.47    inference(superposition,[],[f51,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) ) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~spl3_6 | spl3_7 | ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f40,f50,f44])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_5 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) ) | ~spl3_5),
% 0.21/0.47    inference(resolution,[],[f22,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f44])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    sK0 != sK1 & r1_tarski(sK1,k2_relat_1(sK2)) & r1_tarski(sK0,k2_relat_1(sK2)) & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (X0 != X1 & r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK0 != sK1 & r1_tarski(sK1,k2_relat_1(sK2)) & r1_tarski(sK0,k2_relat_1(sK2)) & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (X0 != X1 & r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((X0 != X1 & (r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f40])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f28])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f24])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (13777)------------------------------
% 0.21/0.47  % (13777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13777)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (13777)Memory used [KB]: 10618
% 0.21/0.47  % (13777)Time elapsed: 0.054 s
% 0.21/0.47  % (13777)------------------------------
% 0.21/0.47  % (13777)------------------------------
% 0.21/0.47  % (13770)Success in time 0.109 s
%------------------------------------------------------------------------------
