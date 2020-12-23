%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 473 expanded)
%              Number of leaves         :   11 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  174 (1280 expanded)
%              Number of equality atoms :   34 ( 174 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f107,f238,f318])).

fof(f318,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f40,f312,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f312,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f302,f302,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f302,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl10_1
    | spl10_2 ),
    inference(forward_demodulation,[],[f296,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl10_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f296,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f21,f241,f252,f49])).

fof(f49,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f252,plain,
    ( r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f240,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f240,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f66,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f241,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f66,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f238,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl10_1
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f62,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f222,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f21,f124,f124,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK9(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f124,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_2 ),
    inference(superposition,[],[f105,f40])).

fof(f105,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = X0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f86,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f74,f26])).

fof(f74,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f69,f70])).

fof(f70,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f67,f23])).

fof(f67,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f69,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f100,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f86,f44])).

fof(f222,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f219,f147])).

fof(f147,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f141,f142])).

fof(f141,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f21,f105,f124,f36])).

fof(f219,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl10_2 ),
    inference(superposition,[],[f52,f70])).

fof(f52,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f21,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f62,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f107,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f20,f65,f61])).

fof(f20,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f19,f65,f61])).

fof(f19,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5248)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (5245)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5250)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (5257)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (5253)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (5241)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (5245)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (5243)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (5266)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (5263)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (5244)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (5256)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (5242)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (5264)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (5252)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (5249)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (5260)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (5246)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (5252)Refutation not found, incomplete strategy% (5252)------------------------------
% 0.20/0.54  % (5252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5252)Memory used [KB]: 10874
% 0.20/0.54  % (5252)Time elapsed: 0.136 s
% 0.20/0.54  % (5252)------------------------------
% 0.20/0.54  % (5252)------------------------------
% 0.20/0.54  % (5263)Refutation not found, incomplete strategy% (5263)------------------------------
% 0.20/0.54  % (5263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5263)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5263)Memory used [KB]: 10746
% 0.20/0.54  % (5263)Time elapsed: 0.128 s
% 0.20/0.54  % (5263)------------------------------
% 0.20/0.54  % (5263)------------------------------
% 0.20/0.54  % (5262)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (5267)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (5251)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f320,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f68,f107,f238,f318])).
% 0.20/0.55  fof(f318,plain,(
% 0.20/0.55    ~spl10_1 | spl10_2),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f317])).
% 0.20/0.55  fof(f317,plain,(
% 0.20/0.55    $false | (~spl10_1 | spl10_2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f40,f312,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.55  fof(f312,plain,(
% 0.20/0.55    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl10_1 | spl10_2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f302,f302,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.55  fof(f302,plain,(
% 0.20/0.55    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl10_1 | spl10_2)),
% 0.20/0.55    inference(forward_demodulation,[],[f296,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl10_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    spl10_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f21,f241,f252,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1) | spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f240,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f66,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl10_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    spl10_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f66,f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    v1_relat_1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    spl10_1 | ~spl10_2),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    $false | (spl10_1 | ~spl10_2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f62,f223])).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl10_2),
% 0.20/0.55    inference(forward_demodulation,[],[f222,f142])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f21,f124,f124,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl10_2),
% 0.20/0.55    inference(superposition,[],[f105,f40])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) ) | ~spl10_2),
% 0.20/0.55    inference(forward_demodulation,[],[f100,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = X0) ) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f86,f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))) ) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f74,f26])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))) ) | ~spl10_2),
% 0.20/0.55    inference(forward_demodulation,[],[f69,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f67,f23])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl10_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f65])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))) ) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f67,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f27,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))))) ) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f86,f44])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl10_2),
% 0.20/0.55    inference(forward_demodulation,[],[f219,f147])).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl10_2),
% 0.20/0.55    inference(forward_demodulation,[],[f141,f142])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,X0) = k10_relat_1(sK1,k1_xboole_0)) ) | ~spl10_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f21,f105,f124,f36])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) | ~spl10_2),
% 0.20/0.55    inference(superposition,[],[f52,f70])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)))) )),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f21,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f33,f42])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl10_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f61])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~spl10_1 | ~spl10_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f20,f65,f61])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    spl10_1 | spl10_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f19,f65,f61])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (5245)------------------------------
% 0.20/0.55  % (5245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5245)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (5245)Memory used [KB]: 6396
% 0.20/0.55  % (5245)Time elapsed: 0.127 s
% 0.20/0.55  % (5245)------------------------------
% 0.20/0.55  % (5245)------------------------------
% 0.20/0.55  % (5240)Success in time 0.195 s
%------------------------------------------------------------------------------
