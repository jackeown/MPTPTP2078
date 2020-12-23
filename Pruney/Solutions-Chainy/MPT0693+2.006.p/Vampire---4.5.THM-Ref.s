%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 189 expanded)
%              Number of equality atoms :   37 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f55,f61,f90])).

fof(f90,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(trivial_inequality_removal,[],[f88])).

fof(f88,plain,
    ( k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(forward_demodulation,[],[f85,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f85,plain,
    ( k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) != k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(superposition,[],[f60,f69])).

fof(f69,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)) = k9_relat_1(sK1,k10_relat_1(sK1,X0))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f62,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f42,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)) = k9_relat_1(sK1,k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f42,f37,f27,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f37,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_5
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f61,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f56,f51,f30,f58])).

fof(f30,plain,
    ( spl2_1
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_4
  <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1)))
    | spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f32,f53])).

fof(f53,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f32,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f55,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f49,f40,f51])).

fof(f49,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f20,f42])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

% (16725)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f16,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f30])).

fof(f26,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1204027392)
% 0.13/0.37  ipcrm: permission denied for id (1204289540)
% 0.13/0.37  ipcrm: permission denied for id (1204322309)
% 0.13/0.37  ipcrm: permission denied for id (1204387847)
% 0.13/0.38  ipcrm: permission denied for id (1204453385)
% 0.13/0.38  ipcrm: permission denied for id (1208418314)
% 0.13/0.38  ipcrm: permission denied for id (1208451083)
% 0.13/0.38  ipcrm: permission denied for id (1208483852)
% 0.13/0.38  ipcrm: permission denied for id (1208516621)
% 0.13/0.38  ipcrm: permission denied for id (1204649999)
% 0.13/0.38  ipcrm: permission denied for id (1208582160)
% 0.13/0.39  ipcrm: permission denied for id (1204715537)
% 0.13/0.39  ipcrm: permission denied for id (1208647698)
% 0.13/0.39  ipcrm: permission denied for id (1204781075)
% 0.13/0.39  ipcrm: permission denied for id (1208680468)
% 0.13/0.39  ipcrm: permission denied for id (1204846613)
% 0.13/0.39  ipcrm: permission denied for id (1208746007)
% 0.13/0.39  ipcrm: permission denied for id (1204944920)
% 0.13/0.40  ipcrm: permission denied for id (1208778777)
% 0.13/0.40  ipcrm: permission denied for id (1205010458)
% 0.13/0.40  ipcrm: permission denied for id (1205075996)
% 0.13/0.40  ipcrm: permission denied for id (1208844317)
% 0.13/0.40  ipcrm: permission denied for id (1205141534)
% 0.13/0.40  ipcrm: permission denied for id (1208877087)
% 0.13/0.40  ipcrm: permission denied for id (1208909856)
% 0.13/0.41  ipcrm: permission denied for id (1205239841)
% 0.13/0.41  ipcrm: permission denied for id (1208942626)
% 0.13/0.41  ipcrm: permission denied for id (1205305379)
% 0.13/0.41  ipcrm: permission denied for id (1205370917)
% 0.13/0.41  ipcrm: permission denied for id (1209008166)
% 0.13/0.42  ipcrm: permission denied for id (1205534762)
% 0.13/0.42  ipcrm: permission denied for id (1209139243)
% 0.20/0.42  ipcrm: permission denied for id (1209204781)
% 0.20/0.42  ipcrm: permission denied for id (1209237550)
% 0.20/0.42  ipcrm: permission denied for id (1205698607)
% 0.20/0.42  ipcrm: permission denied for id (1209303088)
% 0.20/0.43  ipcrm: permission denied for id (1209335857)
% 0.20/0.43  ipcrm: permission denied for id (1209368626)
% 0.20/0.43  ipcrm: permission denied for id (1204060211)
% 0.20/0.43  ipcrm: permission denied for id (1205829684)
% 0.20/0.43  ipcrm: permission denied for id (1209401397)
% 0.20/0.43  ipcrm: permission denied for id (1209434166)
% 0.20/0.44  ipcrm: permission denied for id (1209532473)
% 0.20/0.44  ipcrm: permission denied for id (1209630780)
% 0.20/0.44  ipcrm: permission denied for id (1206157374)
% 0.20/0.44  ipcrm: permission denied for id (1206190143)
% 0.20/0.44  ipcrm: permission denied for id (1206222912)
% 0.20/0.45  ipcrm: permission denied for id (1206255681)
% 0.20/0.45  ipcrm: permission denied for id (1206288450)
% 0.20/0.45  ipcrm: permission denied for id (1206321219)
% 0.20/0.45  ipcrm: permission denied for id (1206353988)
% 0.20/0.45  ipcrm: permission denied for id (1206386757)
% 0.20/0.45  ipcrm: permission denied for id (1206419526)
% 0.20/0.45  ipcrm: permission denied for id (1206452295)
% 0.20/0.45  ipcrm: permission denied for id (1206485064)
% 0.20/0.45  ipcrm: permission denied for id (1209696329)
% 0.20/0.46  ipcrm: permission denied for id (1206550602)
% 0.20/0.47  ipcrm: permission denied for id (1209991251)
% 0.20/0.47  ipcrm: permission denied for id (1210024020)
% 0.20/0.47  ipcrm: permission denied for id (1210089558)
% 0.20/0.47  ipcrm: permission denied for id (1207074904)
% 0.20/0.48  ipcrm: permission denied for id (1207107674)
% 0.20/0.48  ipcrm: permission denied for id (1207140443)
% 0.20/0.48  ipcrm: permission denied for id (1207173212)
% 0.20/0.48  ipcrm: permission denied for id (1207205981)
% 0.20/0.48  ipcrm: permission denied for id (1204093022)
% 0.20/0.48  ipcrm: permission denied for id (1210187871)
% 0.20/0.48  ipcrm: permission denied for id (1210220640)
% 0.20/0.49  ipcrm: permission denied for id (1207337058)
% 0.20/0.49  ipcrm: permission denied for id (1207369827)
% 0.20/0.49  ipcrm: permission denied for id (1207402596)
% 0.20/0.49  ipcrm: permission denied for id (1207435365)
% 0.20/0.49  ipcrm: permission denied for id (1207468134)
% 0.20/0.49  ipcrm: permission denied for id (1207500903)
% 0.20/0.49  ipcrm: permission denied for id (1207533672)
% 0.20/0.49  ipcrm: permission denied for id (1210286185)
% 0.20/0.50  ipcrm: permission denied for id (1207697517)
% 0.20/0.50  ipcrm: permission denied for id (1207730286)
% 0.20/0.50  ipcrm: permission denied for id (1207763055)
% 0.20/0.50  ipcrm: permission denied for id (1207795824)
% 0.20/0.50  ipcrm: permission denied for id (1207828593)
% 0.20/0.51  ipcrm: permission denied for id (1207861362)
% 0.20/0.51  ipcrm: permission denied for id (1207894131)
% 0.20/0.51  ipcrm: permission denied for id (1207926900)
% 0.20/0.51  ipcrm: permission denied for id (1207959669)
% 0.20/0.51  ipcrm: permission denied for id (1207992438)
% 0.20/0.51  ipcrm: permission denied for id (1208025207)
% 0.20/0.51  ipcrm: permission denied for id (1208057976)
% 0.20/0.51  ipcrm: permission denied for id (1208090745)
% 0.20/0.51  ipcrm: permission denied for id (1208123514)
% 0.20/0.52  ipcrm: permission denied for id (1210417275)
% 0.20/0.52  ipcrm: permission denied for id (1208189052)
% 0.20/0.52  ipcrm: permission denied for id (1204125822)
% 0.20/0.52  ipcrm: permission denied for id (1204158591)
% 0.20/0.58  % (16720)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.59  % (16720)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f91,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f33,f38,f43,f55,f61,f90])).
% 0.20/0.59  fof(f90,plain,(
% 0.20/0.59    ~spl2_2 | ~spl2_3 | spl2_5),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    $false | (~spl2_2 | ~spl2_3 | spl2_5)),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f88])).
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) | (~spl2_2 | ~spl2_3 | spl2_5)),
% 0.20/0.59    inference(forward_demodulation,[],[f85,f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.59  fof(f85,plain,(
% 0.20/0.59    k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) != k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) | (~spl2_2 | ~spl2_3 | spl2_5)),
% 0.20/0.59    inference(superposition,[],[f60,f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X0] : (k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) | (~spl2_2 | ~spl2_3)),
% 0.20/0.59    inference(forward_demodulation,[],[f66,f62])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) ) | ~spl2_3),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f42,f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X0] : (k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)) = k9_relat_1(sK1,k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))))) ) | (~spl2_2 | ~spl2_3)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f42,f37,f27,f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(flattening,[],[f13])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f21,f23])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) | spl2_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f58])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    spl2_5 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    ~spl2_5 | spl2_1 | ~spl2_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f56,f51,f30,f58])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    spl2_1 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.59  fof(f51,plain,(
% 0.20/0.59    spl2_4 <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))) | (spl2_1 | ~spl2_4)),
% 0.20/0.59    inference(backward_demodulation,[],[f32,f53])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | ~spl2_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f51])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))) | spl2_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f30])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    spl2_4 | ~spl2_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f49,f40,f51])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | ~spl2_3),
% 0.20/0.59    inference(resolution,[],[f20,f42])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,plain,(
% 0.20/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    spl2_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f17,f40])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    v1_relat_1(sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  % (16725)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.59    inference(flattening,[],[f9])).
% 0.20/0.59  fof(f9,plain,(
% 0.20/0.59    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.59    inference(negated_conjecture,[],[f7])).
% 0.20/0.59  fof(f7,conjecture,(
% 0.20/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    spl2_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f18,f35])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    v1_funct_1(sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ~spl2_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f26,f30])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 0.20/0.59    inference(definition_unfolding,[],[f19,f23])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (16720)------------------------------
% 0.20/0.59  % (16720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (16720)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (16720)Memory used [KB]: 6140
% 0.20/0.59  % (16720)Time elapsed: 0.006 s
% 0.20/0.59  % (16720)------------------------------
% 0.20/0.59  % (16720)------------------------------
% 0.20/0.59  % (16575)Success in time 0.232 s
%------------------------------------------------------------------------------
