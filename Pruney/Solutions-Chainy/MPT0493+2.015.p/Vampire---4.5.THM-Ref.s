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
% DateTime   : Thu Dec  3 12:48:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 154 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f65,f69,f84])).

fof(f84,plain,
    ( ~ spl2_2
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_2
    | spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f22,f32,f64,f68,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(k3_xboole_0(X2,X1),X0)
      | k3_xboole_0(X2,X1) = X0 ) ),
    inference(resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f68,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f64,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_6
  <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f32,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f69,plain,
    ( ~ spl2_3
    | spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f60,f35,f67,f35])).

fof(f35,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(superposition,[],[f16,f56])).

fof(f56,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f17,f37])).

fof(f37,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f65,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f59,f35,f25,f62])).

fof(f25,plain,
    ( spl2_1
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f59,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f27,f56])).

fof(f27,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f35])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26968)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (26956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (26960)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (26968)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (26961)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f28,f33,f38,f65,f69,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~spl2_2 | spl2_6 | ~spl2_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    $false | (~spl2_2 | spl2_6 | ~spl2_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f22,f32,f64,f68,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | ~r1_tarski(k3_xboole_0(X2,X1),X0) | k3_xboole_0(X2,X1) = X0) )),
% 0.21/0.48    inference(resolution,[],[f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl2_7 <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    sK0 != k3_xboole_0(k1_relat_1(sK1),sK0) | spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl2_6 <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~spl2_3 | spl2_7 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f35,f67,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.21/0.49    inference(superposition,[],[f16,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_3),
% 0.21/0.49    inference(resolution,[],[f17,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~spl2_6 | spl2_1 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f35,f25,f62])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl2_1 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sK0 != k3_xboole_0(k1_relat_1(sK1),sK0) | (spl2_1 | ~spl2_3)),
% 0.21/0.49    inference(superposition,[],[f27,f56])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f25])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f35])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26968)------------------------------
% 0.21/0.49  % (26968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26968)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26968)Memory used [KB]: 6140
% 0.21/0.49  % (26968)Time elapsed: 0.066 s
% 0.21/0.49  % (26968)------------------------------
% 0.21/0.49  % (26968)------------------------------
% 0.21/0.49  % (26952)Success in time 0.127 s
%------------------------------------------------------------------------------
