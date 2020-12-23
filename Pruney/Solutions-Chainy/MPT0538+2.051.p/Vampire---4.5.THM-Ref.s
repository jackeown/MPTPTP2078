%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 155 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f55,f60,f71,f78,f83])).

fof(f83,plain,
    ( spl1_1
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl1_1
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_12 ),
    inference(superposition,[],[f23,f76])).

fof(f76,plain,
    ( ! [X1] : k1_xboole_0 = k8_relat_1(X1,k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl1_12
  <=> ! [X1] : k1_xboole_0 = k8_relat_1(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f23,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f78,plain,
    ( spl1_12
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f73,f69,f35,f75])).

fof(f35,plain,
    ( spl1_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f69,plain,
    ( spl1_11
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f73,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(superposition,[],[f36,f70])).

fof(f70,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f36,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f71,plain,
    ( spl1_11
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f63,f58,f52,f69])).

% (22318)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f52,plain,
    ( spl1_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f58,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f63,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0)
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(resolution,[],[f59,f54])).

fof(f54,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl1_9
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f56,f43,f39,f58])).

fof(f39,plain,
    ( spl1_5
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f43,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f55,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f50,f31,f26,f52])).

fof(f26,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f31,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f32,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f45,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f37,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f33,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f29,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f24,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (810614784)
% 0.14/0.37  ipcrm: permission denied for id (813727747)
% 0.14/0.37  ipcrm: permission denied for id (810680324)
% 0.14/0.37  ipcrm: permission denied for id (813760517)
% 0.14/0.37  ipcrm: permission denied for id (810713096)
% 0.14/0.37  ipcrm: permission denied for id (813858825)
% 0.14/0.38  ipcrm: permission denied for id (813891594)
% 0.14/0.38  ipcrm: permission denied for id (813924363)
% 0.14/0.38  ipcrm: permission denied for id (813957132)
% 0.14/0.38  ipcrm: permission denied for id (810844173)
% 0.14/0.38  ipcrm: permission denied for id (810876942)
% 0.14/0.38  ipcrm: permission denied for id (810909711)
% 0.14/0.38  ipcrm: permission denied for id (813989904)
% 0.14/0.39  ipcrm: permission denied for id (814088211)
% 0.14/0.39  ipcrm: permission denied for id (814153749)
% 0.14/0.39  ipcrm: permission denied for id (814186518)
% 0.14/0.39  ipcrm: permission denied for id (811073559)
% 0.14/0.39  ipcrm: permission denied for id (811139097)
% 0.14/0.39  ipcrm: permission denied for id (814252058)
% 0.14/0.40  ipcrm: permission denied for id (814284827)
% 0.21/0.40  ipcrm: permission denied for id (814350365)
% 0.21/0.40  ipcrm: permission denied for id (811204638)
% 0.21/0.40  ipcrm: permission denied for id (811237407)
% 0.21/0.40  ipcrm: permission denied for id (811270176)
% 0.21/0.40  ipcrm: permission denied for id (814383137)
% 0.21/0.41  ipcrm: permission denied for id (811335715)
% 0.21/0.41  ipcrm: permission denied for id (811368484)
% 0.21/0.41  ipcrm: permission denied for id (811401253)
% 0.21/0.41  ipcrm: permission denied for id (811434022)
% 0.21/0.41  ipcrm: permission denied for id (814612522)
% 0.21/0.42  ipcrm: permission denied for id (814645291)
% 0.21/0.42  ipcrm: permission denied for id (814678060)
% 0.21/0.42  ipcrm: permission denied for id (811565101)
% 0.21/0.42  ipcrm: permission denied for id (814710830)
% 0.21/0.42  ipcrm: permission denied for id (811630640)
% 0.21/0.43  ipcrm: permission denied for id (814809138)
% 0.21/0.43  ipcrm: permission denied for id (811696179)
% 0.21/0.43  ipcrm: permission denied for id (811761717)
% 0.21/0.43  ipcrm: permission denied for id (814874678)
% 0.21/0.43  ipcrm: permission denied for id (811827255)
% 0.21/0.43  ipcrm: permission denied for id (814907448)
% 0.21/0.43  ipcrm: permission denied for id (811892793)
% 0.21/0.44  ipcrm: permission denied for id (814940218)
% 0.21/0.44  ipcrm: permission denied for id (811925563)
% 0.21/0.44  ipcrm: permission denied for id (815136833)
% 0.21/0.45  ipcrm: permission denied for id (815169602)
% 0.21/0.45  ipcrm: permission denied for id (812122180)
% 0.21/0.45  ipcrm: permission denied for id (812154950)
% 0.21/0.45  ipcrm: permission denied for id (812187719)
% 0.21/0.45  ipcrm: permission denied for id (812220488)
% 0.21/0.45  ipcrm: permission denied for id (812253257)
% 0.21/0.46  ipcrm: permission denied for id (812318795)
% 0.21/0.46  ipcrm: permission denied for id (815300684)
% 0.21/0.46  ipcrm: permission denied for id (815366222)
% 0.21/0.46  ipcrm: permission denied for id (815431760)
% 0.21/0.47  ipcrm: permission denied for id (812384338)
% 0.21/0.47  ipcrm: permission denied for id (812417107)
% 0.21/0.47  ipcrm: permission denied for id (815497300)
% 0.21/0.47  ipcrm: permission denied for id (815530069)
% 0.21/0.47  ipcrm: permission denied for id (815562838)
% 0.21/0.47  ipcrm: permission denied for id (812548183)
% 0.21/0.47  ipcrm: permission denied for id (815595608)
% 0.21/0.48  ipcrm: permission denied for id (812613722)
% 0.21/0.48  ipcrm: permission denied for id (812744797)
% 0.21/0.48  ipcrm: permission denied for id (815726686)
% 0.21/0.49  ipcrm: permission denied for id (812810336)
% 0.21/0.49  ipcrm: permission denied for id (812843105)
% 0.21/0.49  ipcrm: permission denied for id (812875874)
% 0.21/0.49  ipcrm: permission denied for id (812908643)
% 0.21/0.49  ipcrm: permission denied for id (812941412)
% 0.21/0.49  ipcrm: permission denied for id (812974181)
% 0.21/0.49  ipcrm: permission denied for id (813006950)
% 0.21/0.50  ipcrm: permission denied for id (815825000)
% 0.21/0.50  ipcrm: permission denied for id (813105257)
% 0.21/0.50  ipcrm: permission denied for id (813138027)
% 0.21/0.50  ipcrm: permission denied for id (815890540)
% 0.21/0.50  ipcrm: permission denied for id (813203565)
% 0.21/0.51  ipcrm: permission denied for id (813269104)
% 0.21/0.51  ipcrm: permission denied for id (816021618)
% 0.21/0.51  ipcrm: permission denied for id (813334643)
% 0.21/0.51  ipcrm: permission denied for id (816054388)
% 0.21/0.51  ipcrm: permission denied for id (816087157)
% 0.21/0.51  ipcrm: permission denied for id (813400182)
% 0.21/0.51  ipcrm: permission denied for id (816119927)
% 0.21/0.52  ipcrm: permission denied for id (816152696)
% 0.21/0.52  ipcrm: permission denied for id (816185465)
% 0.21/0.52  ipcrm: permission denied for id (816218234)
% 0.21/0.52  ipcrm: permission denied for id (816283772)
% 0.21/0.52  ipcrm: permission denied for id (816349310)
% 0.21/0.53  ipcrm: permission denied for id (813629567)
% 0.21/0.58  % (22320)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.80/0.61  % (22321)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.80/0.61  % (22319)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.80/0.61  % (22325)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.80/0.61  % (22313)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.80/0.61  % (22319)Refutation found. Thanks to Tanya!
% 0.80/0.61  % SZS status Theorem for theBenchmark
% 0.80/0.61  % SZS output start Proof for theBenchmark
% 0.80/0.61  fof(f85,plain,(
% 0.80/0.61    $false),
% 0.80/0.61    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f55,f60,f71,f78,f83])).
% 0.80/0.61  fof(f83,plain,(
% 0.80/0.61    spl1_1 | ~spl1_12),
% 0.80/0.61    inference(avatar_contradiction_clause,[],[f82])).
% 0.80/0.61  fof(f82,plain,(
% 0.80/0.61    $false | (spl1_1 | ~spl1_12)),
% 0.80/0.61    inference(trivial_inequality_removal,[],[f79])).
% 0.80/0.61  fof(f79,plain,(
% 0.80/0.61    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_12)),
% 0.80/0.61    inference(superposition,[],[f23,f76])).
% 0.80/0.61  fof(f76,plain,(
% 0.80/0.61    ( ! [X1] : (k1_xboole_0 = k8_relat_1(X1,k1_xboole_0)) ) | ~spl1_12),
% 0.80/0.61    inference(avatar_component_clause,[],[f75])).
% 0.80/0.61  fof(f75,plain,(
% 0.80/0.61    spl1_12 <=> ! [X1] : k1_xboole_0 = k8_relat_1(X1,k1_xboole_0)),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.80/0.61  fof(f23,plain,(
% 0.80/0.61    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.80/0.61    inference(avatar_component_clause,[],[f21])).
% 0.80/0.61  fof(f21,plain,(
% 0.80/0.61    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.80/0.61  fof(f78,plain,(
% 0.80/0.61    spl1_12 | ~spl1_4 | ~spl1_11),
% 0.80/0.61    inference(avatar_split_clause,[],[f73,f69,f35,f75])).
% 0.80/0.61  fof(f35,plain,(
% 0.80/0.61    spl1_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.80/0.61  fof(f69,plain,(
% 0.80/0.61    spl1_11 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0)),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.80/0.61  fof(f73,plain,(
% 0.80/0.61    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_11)),
% 0.80/0.61    inference(superposition,[],[f36,f70])).
% 0.80/0.61  fof(f70,plain,(
% 0.80/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0)) ) | ~spl1_11),
% 0.80/0.61    inference(avatar_component_clause,[],[f69])).
% 0.80/0.61  fof(f36,plain,(
% 0.80/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_4),
% 0.80/0.61    inference(avatar_component_clause,[],[f35])).
% 0.80/0.61  fof(f71,plain,(
% 0.80/0.61    spl1_11 | ~spl1_8 | ~spl1_9),
% 0.80/0.61    inference(avatar_split_clause,[],[f63,f58,f52,f69])).
% 0.80/0.61  % (22318)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.80/0.61  fof(f52,plain,(
% 0.80/0.61    spl1_8 <=> v1_relat_1(k1_xboole_0)),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.80/0.61  fof(f58,plain,(
% 0.80/0.61    spl1_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.80/0.61  fof(f63,plain,(
% 0.80/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k8_relat_1(X2,k1_xboole_0),k1_xboole_0)) ) | (~spl1_8 | ~spl1_9)),
% 0.80/0.61    inference(resolution,[],[f59,f54])).
% 0.80/0.61  fof(f54,plain,(
% 0.80/0.61    v1_relat_1(k1_xboole_0) | ~spl1_8),
% 0.80/0.61    inference(avatar_component_clause,[],[f52])).
% 0.80/0.61  fof(f59,plain,(
% 0.80/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1)) ) | ~spl1_9),
% 0.80/0.61    inference(avatar_component_clause,[],[f58])).
% 0.80/0.61  fof(f60,plain,(
% 0.80/0.61    spl1_9 | ~spl1_5 | ~spl1_6),
% 0.80/0.61    inference(avatar_split_clause,[],[f56,f43,f39,f58])).
% 0.80/0.61  fof(f39,plain,(
% 0.80/0.61    spl1_5 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.80/0.61  fof(f43,plain,(
% 0.80/0.61    spl1_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.80/0.61  fof(f56,plain,(
% 0.80/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | (~spl1_5 | ~spl1_6)),
% 0.80/0.61    inference(resolution,[],[f44,f40])).
% 0.80/0.61  fof(f40,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl1_5),
% 0.80/0.61    inference(avatar_component_clause,[],[f39])).
% 0.80/0.61  fof(f44,plain,(
% 0.80/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl1_6),
% 0.80/0.61    inference(avatar_component_clause,[],[f43])).
% 0.80/0.61  fof(f55,plain,(
% 0.80/0.61    spl1_8 | ~spl1_2 | ~spl1_3),
% 0.80/0.61    inference(avatar_split_clause,[],[f50,f31,f26,f52])).
% 0.80/0.61  fof(f26,plain,(
% 0.80/0.61    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.80/0.61  fof(f31,plain,(
% 0.80/0.61    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.80/0.61    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.80/0.61  fof(f50,plain,(
% 0.80/0.61    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.80/0.61    inference(superposition,[],[f32,f28])).
% 0.80/0.61  fof(f28,plain,(
% 0.80/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.80/0.61    inference(avatar_component_clause,[],[f26])).
% 0.80/0.61  fof(f32,plain,(
% 0.80/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.80/0.61    inference(avatar_component_clause,[],[f31])).
% 0.80/0.61  fof(f45,plain,(
% 0.80/0.61    spl1_6),
% 0.80/0.61    inference(avatar_split_clause,[],[f19,f43])).
% 0.80/0.61  fof(f19,plain,(
% 0.80/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f12])).
% 0.80/0.61  fof(f12,plain,(
% 0.80/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.80/0.61    inference(nnf_transformation,[],[f1])).
% 0.80/0.61  fof(f1,axiom,(
% 0.80/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.80/0.61  fof(f41,plain,(
% 0.80/0.61    spl1_5),
% 0.80/0.61    inference(avatar_split_clause,[],[f17,f39])).
% 0.80/0.61  fof(f17,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f9])).
% 0.80/0.61  fof(f9,plain,(
% 0.80/0.61    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.80/0.61    inference(ennf_transformation,[],[f4])).
% 0.80/0.61  fof(f4,axiom,(
% 0.80/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.80/0.61  fof(f37,plain,(
% 0.80/0.61    spl1_4),
% 0.80/0.61    inference(avatar_split_clause,[],[f16,f35])).
% 0.80/0.61  fof(f16,plain,(
% 0.80/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.80/0.61    inference(cnf_transformation,[],[f2])).
% 0.80/0.61  fof(f2,axiom,(
% 0.80/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.80/0.61  fof(f33,plain,(
% 0.80/0.61    spl1_3),
% 0.80/0.61    inference(avatar_split_clause,[],[f15,f31])).
% 0.80/0.61  fof(f15,plain,(
% 0.80/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.80/0.61    inference(cnf_transformation,[],[f3])).
% 0.80/0.61  fof(f3,axiom,(
% 0.80/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.80/0.61  fof(f29,plain,(
% 0.80/0.61    spl1_2),
% 0.80/0.61    inference(avatar_split_clause,[],[f14,f26])).
% 0.80/0.61  fof(f14,plain,(
% 0.80/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.80/0.61    inference(cnf_transformation,[],[f5])).
% 0.80/0.61  fof(f5,axiom,(
% 0.80/0.61    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.80/0.61  fof(f24,plain,(
% 0.80/0.61    ~spl1_1),
% 0.80/0.61    inference(avatar_split_clause,[],[f13,f21])).
% 0.80/0.61  fof(f13,plain,(
% 0.80/0.61    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.80/0.61    inference(cnf_transformation,[],[f11])).
% 0.80/0.61  fof(f11,plain,(
% 0.80/0.61    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.80/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.80/0.61  fof(f10,plain,(
% 0.80/0.61    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.80/0.61    introduced(choice_axiom,[])).
% 0.80/0.61  fof(f8,plain,(
% 0.80/0.61    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.80/0.61    inference(ennf_transformation,[],[f7])).
% 0.80/0.61  fof(f7,negated_conjecture,(
% 0.80/0.61    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.80/0.61    inference(negated_conjecture,[],[f6])).
% 0.80/0.61  fof(f6,conjecture,(
% 0.80/0.61    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.80/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.80/0.61  % SZS output end Proof for theBenchmark
% 0.80/0.61  % (22319)------------------------------
% 0.80/0.61  % (22319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.61  % (22319)Termination reason: Refutation
% 0.80/0.61  
% 0.80/0.61  % (22319)Memory used [KB]: 10618
% 0.80/0.61  % (22319)Time elapsed: 0.027 s
% 0.80/0.61  % (22319)------------------------------
% 0.80/0.61  % (22319)------------------------------
% 0.80/0.61  % (22322)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.80/0.62  % (22128)Success in time 0.255 s
%------------------------------------------------------------------------------
