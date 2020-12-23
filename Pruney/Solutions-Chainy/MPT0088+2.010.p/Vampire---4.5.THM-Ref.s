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
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 158 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 374 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f38,f97,f102,f159,f236,f303,f475,f663,f702,f718])).

fof(f718,plain,
    ( spl3_2
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f716,f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f716,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_11 ),
    inference(resolution,[],[f701,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f701,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f699])).

fof(f699,plain,
    ( spl3_11
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f702,plain,
    ( spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f682,f660,f699])).

fof(f660,plain,
    ( spl3_10
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f682,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f662,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f662,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f660])).

fof(f663,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f653,f35,f660])).

fof(f35,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f653,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f652,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f652,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f649,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f649,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f381,f92])).

fof(f92,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(k4_xboole_0(X8,X6),k4_xboole_0(X7,X6))
      | r1_xboole_0(k4_xboole_0(X8,X6),k2_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f56,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))
      | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ) ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f381,plain,
    ( ! [X0] :
        ( r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2))
        | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f180,f83])).

fof(f83,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_xboole_0(X4,k2_xboole_0(X5,X6))
      | r1_xboole_0(k4_xboole_0(X6,X5),X4) ) ),
    inference(resolution,[],[f47,f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k4_xboole_0(X1,X0))
      | ~ r1_xboole_0(X2,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f21,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f180,plain,
    ( ! [X0] :
        ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(X0,sK0))
        | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f58,f16])).

fof(f58,plain,
    ( ! [X8] :
        ( r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X8))
        | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),X8) )
    | ~ spl3_3 ),
    inference(resolution,[],[f19,f37])).

fof(f37,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f475,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f110,f99,f23,f472])).

fof(f472,plain,
    ( spl3_9
  <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f23,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f99,plain,
    ( spl3_5
  <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f110,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f101,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f303,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f247,f233,f300])).

fof(f300,plain,
    ( spl3_8
  <=> r1_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f233,plain,
    ( spl3_7
  <=> r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f247,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_7 ),
    inference(resolution,[],[f235,f18])).

fof(f235,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f233])).

fof(f236,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f211,f99,f233])).

fof(f211,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f83,f101])).

fof(f159,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f114,f99,f156])).

fof(f156,plain,
    ( spl3_6
  <=> r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f18])).

fof(f102,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f72,f23,f99])).

fof(f72,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f55,f25])).

fof(f97,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f85,f28,f94])).

fof(f94,plain,
    ( spl3_4
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f81,f16])).

fof(f81,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | spl3_2 ),
    inference(resolution,[],[f47,f30])).

fof(f38,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f23,f35])).

fof(f32,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f18,f25])).

fof(f31,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:35:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (812089344)
% 0.15/0.37  ipcrm: permission denied for id (812122115)
% 0.15/0.39  ipcrm: permission denied for id (812351507)
% 0.15/0.40  ipcrm: permission denied for id (812384279)
% 0.15/0.40  ipcrm: permission denied for id (812417052)
% 0.15/0.40  ipcrm: permission denied for id (812449822)
% 0.15/0.41  ipcrm: permission denied for id (812515362)
% 0.15/0.41  ipcrm: permission denied for id (812580902)
% 0.15/0.42  ipcrm: permission denied for id (812646442)
% 0.22/0.43  ipcrm: permission denied for id (812744754)
% 0.22/0.43  ipcrm: permission denied for id (812843063)
% 0.22/0.44  ipcrm: permission denied for id (813039680)
% 0.22/0.45  ipcrm: permission denied for id (813105219)
% 0.22/0.45  ipcrm: permission denied for id (813137989)
% 0.22/0.45  ipcrm: permission denied for id (813170759)
% 0.22/0.45  ipcrm: permission denied for id (813203528)
% 0.22/0.46  ipcrm: permission denied for id (813269070)
% 0.22/0.46  ipcrm: permission denied for id (813301839)
% 0.22/0.47  ipcrm: permission denied for id (813367382)
% 0.22/0.48  ipcrm: permission denied for id (813498466)
% 0.22/0.49  ipcrm: permission denied for id (813596774)
% 0.22/0.49  ipcrm: permission denied for id (813727853)
% 0.22/0.50  ipcrm: permission denied for id (813760623)
% 0.22/0.50  ipcrm: permission denied for id (813826164)
% 0.22/0.50  ipcrm: permission denied for id (813858933)
% 0.22/0.51  ipcrm: permission denied for id (813957244)
% 0.22/0.52  ipcrm: permission denied for id (814022783)
% 0.67/0.58  % (19882)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.67/0.59  % (19883)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.82/0.60  % (19878)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.82/0.60  % (19877)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.82/0.60  % (19885)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.82/0.60  % (19880)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.82/0.61  % (19875)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.82/0.61  % (19879)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.82/0.61  % (19874)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.82/0.62  % (19884)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.82/0.63  % (19881)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.82/0.63  % (19876)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.82/0.64  % (19882)Refutation not found, incomplete strategy% (19882)------------------------------
% 0.82/0.64  % (19882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.82/0.64  % (19882)Termination reason: Refutation not found, incomplete strategy
% 0.82/0.64  
% 0.82/0.64  % (19882)Memory used [KB]: 6012
% 0.82/0.64  % (19882)Time elapsed: 0.056 s
% 0.82/0.64  % (19882)------------------------------
% 0.82/0.64  % (19882)------------------------------
% 1.69/0.71  % (19880)Refutation found. Thanks to Tanya!
% 1.69/0.71  % SZS status Theorem for theBenchmark
% 1.69/0.71  % SZS output start Proof for theBenchmark
% 1.69/0.71  fof(f719,plain,(
% 1.69/0.71    $false),
% 1.69/0.71    inference(avatar_sat_refutation,[],[f26,f31,f38,f97,f102,f159,f236,f303,f475,f663,f702,f718])).
% 1.69/0.71  fof(f718,plain,(
% 1.69/0.71    spl3_2 | ~spl3_11),
% 1.69/0.71    inference(avatar_contradiction_clause,[],[f717])).
% 1.69/0.71  fof(f717,plain,(
% 1.69/0.71    $false | (spl3_2 | ~spl3_11)),
% 1.69/0.71    inference(subsumption_resolution,[],[f716,f30])).
% 1.69/0.71  fof(f30,plain,(
% 1.69/0.71    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 1.69/0.71    inference(avatar_component_clause,[],[f28])).
% 1.69/0.71  fof(f28,plain,(
% 1.69/0.71    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.69/0.71  fof(f716,plain,(
% 1.69/0.71    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_11),
% 1.69/0.71    inference(resolution,[],[f701,f18])).
% 1.69/0.71  fof(f18,plain,(
% 1.69/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.69/0.71    inference(cnf_transformation,[],[f9])).
% 1.69/0.71  fof(f9,plain,(
% 1.69/0.71    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.69/0.71    inference(ennf_transformation,[],[f2])).
% 1.69/0.71  fof(f2,axiom,(
% 1.69/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.69/0.71  fof(f701,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_11),
% 1.69/0.71    inference(avatar_component_clause,[],[f699])).
% 1.69/0.71  fof(f699,plain,(
% 1.69/0.71    spl3_11 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.69/0.71  fof(f702,plain,(
% 1.69/0.71    spl3_11 | ~spl3_10),
% 1.69/0.71    inference(avatar_split_clause,[],[f682,f660,f699])).
% 1.69/0.71  fof(f660,plain,(
% 1.69/0.71    spl3_10 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.69/0.71  fof(f682,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_10),
% 1.69/0.71    inference(resolution,[],[f662,f20])).
% 1.69/0.71  fof(f20,plain,(
% 1.69/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.69/0.71    inference(cnf_transformation,[],[f10])).
% 1.69/0.71  fof(f10,plain,(
% 1.69/0.71    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.69/0.71    inference(ennf_transformation,[],[f4])).
% 1.69/0.71  fof(f4,axiom,(
% 1.69/0.71    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.69/0.71  fof(f662,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_10),
% 1.69/0.71    inference(avatar_component_clause,[],[f660])).
% 1.69/0.71  fof(f663,plain,(
% 1.69/0.71    spl3_10 | ~spl3_3),
% 1.69/0.71    inference(avatar_split_clause,[],[f653,f35,f660])).
% 1.69/0.71  fof(f35,plain,(
% 1.69/0.71    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.69/0.71  fof(f653,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 1.69/0.71    inference(forward_demodulation,[],[f652,f16])).
% 1.69/0.71  fof(f16,plain,(
% 1.69/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.69/0.71    inference(cnf_transformation,[],[f1])).
% 1.69/0.71  fof(f1,axiom,(
% 1.69/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.69/0.71  fof(f652,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1)) | ~spl3_3),
% 1.69/0.71    inference(subsumption_resolution,[],[f649,f15])).
% 1.69/0.71  fof(f15,plain,(
% 1.69/0.71    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.69/0.71    inference(cnf_transformation,[],[f5])).
% 1.69/0.71  fof(f5,axiom,(
% 1.69/0.71    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.69/0.71  fof(f649,plain,(
% 1.69/0.71    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) | r1_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1)) | ~spl3_3),
% 1.69/0.71    inference(resolution,[],[f381,f92])).
% 1.69/0.71  fof(f92,plain,(
% 1.69/0.71    ( ! [X6,X8,X7] : (~r1_xboole_0(k4_xboole_0(X8,X6),k4_xboole_0(X7,X6)) | r1_xboole_0(k4_xboole_0(X8,X6),k2_xboole_0(X6,X7))) )),
% 1.69/0.71    inference(superposition,[],[f56,f17])).
% 1.69/0.71  fof(f17,plain,(
% 1.69/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.69/0.71    inference(cnf_transformation,[],[f3])).
% 1.69/0.71  fof(f3,axiom,(
% 1.69/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.69/0.71  fof(f56,plain,(
% 1.69/0.71    ( ! [X2,X3,X1] : (r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3)) | ~r1_xboole_0(k4_xboole_0(X1,X2),X3)) )),
% 1.69/0.71    inference(resolution,[],[f19,f15])).
% 1.69/0.71  fof(f19,plain,(
% 1.69/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.69/0.71    inference(cnf_transformation,[],[f10])).
% 1.69/0.71  fof(f381,plain,(
% 1.69/0.71    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),X0)) ) | ~spl3_3),
% 1.69/0.71    inference(resolution,[],[f180,f83])).
% 1.69/0.71  fof(f83,plain,(
% 1.69/0.71    ( ! [X6,X4,X5] : (~r1_xboole_0(X4,k2_xboole_0(X5,X6)) | r1_xboole_0(k4_xboole_0(X6,X5),X4)) )),
% 1.69/0.71    inference(resolution,[],[f47,f18])).
% 1.69/0.71  fof(f47,plain,(
% 1.69/0.71    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k4_xboole_0(X1,X0)) | ~r1_xboole_0(X2,k2_xboole_0(X0,X1))) )),
% 1.69/0.71    inference(superposition,[],[f21,f17])).
% 1.69/0.71  fof(f21,plain,(
% 1.69/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.69/0.71    inference(cnf_transformation,[],[f10])).
% 1.69/0.71  fof(f180,plain,(
% 1.69/0.71    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(X0,sK0)) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),X0)) ) | ~spl3_3),
% 1.69/0.71    inference(superposition,[],[f58,f16])).
% 1.69/0.71  fof(f58,plain,(
% 1.69/0.71    ( ! [X8] : (r1_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X8)) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),X8)) ) | ~spl3_3),
% 1.69/0.71    inference(resolution,[],[f19,f37])).
% 1.69/0.71  fof(f37,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_3),
% 1.69/0.71    inference(avatar_component_clause,[],[f35])).
% 1.69/0.71  fof(f475,plain,(
% 1.69/0.71    spl3_9 | ~spl3_1 | ~spl3_5),
% 1.69/0.71    inference(avatar_split_clause,[],[f110,f99,f23,f472])).
% 1.69/0.71  fof(f472,plain,(
% 1.69/0.71    spl3_9 <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.69/0.71  fof(f23,plain,(
% 1.69/0.71    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.69/0.71  fof(f99,plain,(
% 1.69/0.71    spl3_5 <=> r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.69/0.71  fof(f110,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))) | (~spl3_1 | ~spl3_5)),
% 1.69/0.71    inference(resolution,[],[f101,f55])).
% 1.69/0.71  fof(f55,plain,(
% 1.69/0.71    ( ! [X0] : (~r1_xboole_0(sK0,X0) | r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0))) ) | ~spl3_1),
% 1.69/0.71    inference(resolution,[],[f19,f25])).
% 1.69/0.71  fof(f25,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.69/0.71    inference(avatar_component_clause,[],[f23])).
% 1.69/0.71  fof(f101,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_5),
% 1.69/0.71    inference(avatar_component_clause,[],[f99])).
% 1.69/0.71  fof(f303,plain,(
% 1.69/0.71    spl3_8 | ~spl3_7),
% 1.69/0.71    inference(avatar_split_clause,[],[f247,f233,f300])).
% 1.69/0.71  fof(f300,plain,(
% 1.69/0.71    spl3_8 <=> r1_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.69/0.71  fof(f233,plain,(
% 1.69/0.71    spl3_7 <=> r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0)),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.69/0.71  fof(f247,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_7),
% 1.69/0.71    inference(resolution,[],[f235,f18])).
% 1.69/0.71  fof(f235,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0) | ~spl3_7),
% 1.69/0.71    inference(avatar_component_clause,[],[f233])).
% 1.69/0.71  fof(f236,plain,(
% 1.69/0.71    spl3_7 | ~spl3_5),
% 1.69/0.71    inference(avatar_split_clause,[],[f211,f99,f233])).
% 1.69/0.71  fof(f211,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0) | ~spl3_5),
% 1.69/0.71    inference(resolution,[],[f83,f101])).
% 1.69/0.71  fof(f159,plain,(
% 1.69/0.71    spl3_6 | ~spl3_5),
% 1.69/0.71    inference(avatar_split_clause,[],[f114,f99,f156])).
% 1.69/0.71  fof(f156,plain,(
% 1.69/0.71    spl3_6 <=> r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0)),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.69/0.71  fof(f114,plain,(
% 1.69/0.71    r1_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),sK0) | ~spl3_5),
% 1.69/0.71    inference(resolution,[],[f101,f18])).
% 1.69/0.71  fof(f102,plain,(
% 1.69/0.71    spl3_5 | ~spl3_1),
% 1.69/0.71    inference(avatar_split_clause,[],[f72,f23,f99])).
% 1.69/0.71  fof(f72,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.69/0.71    inference(resolution,[],[f55,f25])).
% 1.69/0.71  fof(f97,plain,(
% 1.69/0.71    ~spl3_4 | spl3_2),
% 1.69/0.71    inference(avatar_split_clause,[],[f85,f28,f94])).
% 1.69/0.71  fof(f94,plain,(
% 1.69/0.71    spl3_4 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.69/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.69/0.71  fof(f85,plain,(
% 1.69/0.71    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl3_2),
% 1.69/0.71    inference(forward_demodulation,[],[f81,f16])).
% 1.69/0.71  fof(f81,plain,(
% 1.69/0.71    ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | spl3_2),
% 1.69/0.71    inference(resolution,[],[f47,f30])).
% 1.69/0.71  fof(f38,plain,(
% 1.69/0.71    spl3_3 | ~spl3_1),
% 1.69/0.71    inference(avatar_split_clause,[],[f32,f23,f35])).
% 1.69/0.71  fof(f32,plain,(
% 1.69/0.71    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_1),
% 1.69/0.71    inference(resolution,[],[f18,f25])).
% 1.69/0.71  fof(f31,plain,(
% 1.69/0.71    ~spl3_2),
% 1.69/0.71    inference(avatar_split_clause,[],[f14,f28])).
% 1.69/0.71  fof(f14,plain,(
% 1.69/0.71    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.69/0.71    inference(cnf_transformation,[],[f12])).
% 1.69/0.71  fof(f12,plain,(
% 1.69/0.71    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.69/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 1.69/0.71  fof(f11,plain,(
% 1.69/0.71    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.69/0.71    introduced(choice_axiom,[])).
% 1.69/0.71  fof(f8,plain,(
% 1.69/0.71    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.69/0.71    inference(ennf_transformation,[],[f7])).
% 1.69/0.71  fof(f7,negated_conjecture,(
% 1.69/0.71    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.69/0.71    inference(negated_conjecture,[],[f6])).
% 1.69/0.71  fof(f6,conjecture,(
% 1.69/0.71    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.69/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.69/0.71  fof(f26,plain,(
% 1.69/0.71    spl3_1),
% 1.69/0.71    inference(avatar_split_clause,[],[f13,f23])).
% 1.69/0.71  fof(f13,plain,(
% 1.69/0.71    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.69/0.71    inference(cnf_transformation,[],[f12])).
% 1.69/0.71  % SZS output end Proof for theBenchmark
% 1.69/0.71  % (19880)------------------------------
% 1.69/0.71  % (19880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.71  % (19880)Termination reason: Refutation
% 1.69/0.71  
% 1.69/0.71  % (19880)Memory used [KB]: 6908
% 1.69/0.71  % (19880)Time elapsed: 0.114 s
% 1.69/0.71  % (19880)------------------------------
% 1.69/0.71  % (19880)------------------------------
% 1.69/0.72  % (19740)Success in time 0.354 s
%------------------------------------------------------------------------------
