%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 376 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f58,f62,f78,f153,f422,f435])).

fof(f435,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_5
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_5
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f427,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl9_5
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f427,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(resolution,[],[f421,f94])).

fof(f94,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k8_relat_1(X1,sK3),X2)
        | r1_tarski(k8_relat_1(X1,sK2),X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(resolution,[],[f67,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f67,plain,
    ( ! [X1] : r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f66,f49])).

fof(f49,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl9_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f66,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3)) )
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f65,f45])).

fof(f45,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl9_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f65,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK2)
        | r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

fof(f57,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f421,plain,
    ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl9_23
  <=> r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f422,plain,
    ( spl9_23
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f411,f151,f44,f420])).

fof(f151,plain,
    ( spl9_14
  <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f411,plain,
    ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(superposition,[],[f403,f152])).

fof(f152,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f403,plain,
    ( ! [X4,X3] : r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f74,f401])).

fof(f401,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK3))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f400,f40])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f400,plain,
    ( ! [X0] :
        ( v1_relat_1(k8_relat_1(X0,sK3))
        | sK6(k8_relat_1(X0,sK3)) = k4_tarski(sK7(sK6(k8_relat_1(X0,sK3))),sK8(sK6(k8_relat_1(X0,sK3)))) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f398,f45])).

fof(f398,plain,
    ( ! [X0] :
        ( v1_relat_1(k8_relat_1(X0,sK3))
        | sK6(k8_relat_1(X0,sK3)) = k4_tarski(sK7(sK6(k8_relat_1(X0,sK3))),sK8(sK6(k8_relat_1(X0,sK3))))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_1 ),
    inference(resolution,[],[f265,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_tarski(sK7(X1),sK8(X1)) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f265,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(k8_relat_1(X1,sK3)),sK3)
        | v1_relat_1(k8_relat_1(X1,sK3)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f180,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f180,plain,
    ( ! [X3] :
        ( sP5(sK6(k8_relat_1(X3,sK3)),sK3,k8_relat_1(X3,sK3))
        | v1_relat_1(k8_relat_1(X3,sK3)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f130,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k8_relat_1(X0,sK3))
        | sP5(X1,sK3,k8_relat_1(X0,sK3)) )
    | ~ spl9_1 ),
    inference(superposition,[],[f41,f71])).

fof(f71,plain,
    ( ! [X0] : k8_relat_1(X0,sK3) = k3_xboole_0(k8_relat_1(X0,sK3),sK3)
    | ~ spl9_1 ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK3),sK3)
    | ~ spl9_1 ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(k8_relat_1(X3,sK3))
        | r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f73,f45])).

fof(f73,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(k8_relat_1(X3,sK3))
        | r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f51,f27])).

fof(f153,plain,
    ( spl9_14
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f107,f60,f44,f151])).

fof(f60,plain,
    ( spl9_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f107,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f52,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,X2)
        | k8_relat_1(X1,sK3) = k8_relat_1(X2,k8_relat_1(X1,sK3)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f45,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

% (29319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f78,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f24,f76])).

fof(f24,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

fof(f62,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (29305)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (29311)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (29323)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (29320)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (29317)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (29310)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (29305)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f46,f50,f58,f62,f78,f153,f422,f435])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    ~spl9_1 | ~spl9_2 | ~spl9_3 | spl9_5 | ~spl9_23),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    $false | (~spl9_1 | ~spl9_2 | ~spl9_3 | spl9_5 | ~spl9_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f427,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl9_5 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_23)),
% 0.21/0.50    inference(resolution,[],[f421,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_tarski(k8_relat_1(X1,sK3),X2) | r1_tarski(k8_relat_1(X1,sK2),X2)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.21/0.50    inference(resolution,[],[f67,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl9_2 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(sK2) | r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))) ) | (~spl9_1 | ~spl9_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f65,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl9_1 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(sK3) | ~v1_relat_1(sK2) | r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))) ) | ~spl9_3),
% 0.21/0.50    inference(resolution,[],[f57,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_tarski(sK2,sK3) | ~spl9_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl9_3 <=> r1_tarski(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) | ~spl9_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f420])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    spl9_23 <=> r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl9_23 | ~spl9_1 | ~spl9_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f411,f151,f44,f420])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl9_14 <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) | (~spl9_1 | ~spl9_14)),
% 0.21/0.50    inference(superposition,[],[f403,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | ~spl9_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f151])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    ( ! [X4,X3] : (r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f401])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f400,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK3)) | sK6(k8_relat_1(X0,sK3)) = k4_tarski(sK7(sK6(k8_relat_1(X0,sK3))),sK8(sK6(k8_relat_1(X0,sK3))))) ) | ~spl9_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f398,f45])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK3)) | sK6(k8_relat_1(X0,sK3)) = k4_tarski(sK7(sK6(k8_relat_1(X0,sK3))),sK8(sK6(k8_relat_1(X0,sK3)))) | ~v1_relat_1(sK3)) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f265,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_tarski(sK7(X1),sK8(X1)) = X1 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK6(k8_relat_1(X1,sK3)),sK3) | v1_relat_1(k8_relat_1(X1,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f180,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X3] : (sP5(sK6(k8_relat_1(X3,sK3)),sK3,k8_relat_1(X3,sK3)) | v1_relat_1(k8_relat_1(X3,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f130,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k8_relat_1(X0,sK3)) | sP5(X1,sK3,k8_relat_1(X0,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(superposition,[],[f41,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (k8_relat_1(X0,sK3) = k3_xboole_0(k8_relat_1(X0,sK3),sK3)) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f51,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK3),sK3)) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f45,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~v1_relat_1(k8_relat_1(X3,sK3)) | r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f45])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~v1_relat_1(sK3) | ~v1_relat_1(k8_relat_1(X3,sK3)) | r1_tarski(k8_relat_1(X4,k8_relat_1(X3,sK3)),k8_relat_1(X4,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f51,f27])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl9_14 | ~spl9_1 | ~spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f60,f44,f151])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl9_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | (~spl9_1 | ~spl9_4)),
% 0.21/0.50    inference(resolution,[],[f52,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl9_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k8_relat_1(X1,sK3) = k8_relat_1(X2,k8_relat_1(X1,sK3))) ) | ~spl9_1),
% 0.21/0.50    inference(resolution,[],[f45,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % (29319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f76])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f60])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f56])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r1_tarski(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl9_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f48])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl9_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29305)------------------------------
% 0.21/0.50  % (29305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29305)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29305)Memory used [KB]: 6524
% 0.21/0.50  % (29305)Time elapsed: 0.077 s
% 0.21/0.50  % (29305)------------------------------
% 0.21/0.50  % (29305)------------------------------
% 0.21/0.51  % (29302)Success in time 0.144 s
%------------------------------------------------------------------------------
