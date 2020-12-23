%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 129 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f45,f47])).

fof(f47,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f46,f42,f32,f27])).

fof(f27,plain,
    ( spl1_1
  <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f32,plain,
    ( spl1_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f42,plain,
    ( spl1_3
  <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f46,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f44,f37])).

fof(f37,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f18])).

fof(f18,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f34,plain,
    ( l1_orders_2(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f44,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f39,f32,f42])).

fof(f39,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0))
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f19,f36,f21,f20,f22,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f22,plain,(
    ! [X0,X1] : v1_partfun1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_partfun1(k2_funcop_1(X0,X1),X0)
      & v1_funct_1(k2_funcop_1(X0,X1))
      & v4_relat_1(k2_funcop_1(X0,X1),X0)
      & v1_relat_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).

fof(f20,plain,(
    ! [X0,X1] : v4_relat_1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] : v1_funct_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,
    ( ! [X0] : v1_yellow_1(k2_funcop_1(X0,sK0))
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f19,plain,(
    ! [X0,X1] : v1_relat_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f30,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:06:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (6188)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (6191)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (6198)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (6190)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (6192)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (6191)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f30,f35,f45,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl1_1 | ~spl1_2 | ~spl1_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f46,f42,f32,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    spl1_1 <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl1_2 <=> l1_orders_2(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl1_3 <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0) | (~spl1_2 | ~spl1_3)),
% 0.22/0.47    inference(forward_demodulation,[],[f44,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | ~spl1_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f34,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    l1_orders_2(sK0) | ~spl1_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0)) | ~spl1_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl1_3 | ~spl1_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f32,f42])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK0)) | ~spl1_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f19,f36,f21,f20,f22,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | ~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_partfun1(k2_funcop_1(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_partfun1(k2_funcop_1(X0,X1),X0) & v1_funct_1(k2_funcop_1(X0,X1)) & v4_relat_1(k2_funcop_1(X0,X1),X0) & v1_relat_1(k2_funcop_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v4_relat_1(k2_funcop_1(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_funct_1(k2_funcop_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0] : (v1_yellow_1(k2_funcop_1(X0,sK0))) ) | ~spl1_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f34,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_funcop_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl1_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f32])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    l1_orders_2(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~spl1_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f27])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (6191)------------------------------
% 0.22/0.47  % (6191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (6191)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (6191)Memory used [KB]: 6140
% 0.22/0.47  % (6191)Time elapsed: 0.051 s
% 0.22/0.47  % (6191)------------------------------
% 0.22/0.47  % (6191)------------------------------
% 0.22/0.47  % (6189)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (6196)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (6184)Success in time 0.11 s
%------------------------------------------------------------------------------
