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
% DateTime   : Thu Dec  3 12:34:38 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   31 (  44 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f21,f29,f37,f122,f128])).

fof(f128,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f123,f102])).

fof(f102,plain,
    ( ! [X19,X17,X18,X16] : k2_enumset1(X16,X19,X18,X17) = k2_enumset1(X19,X17,X16,X18)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_11
  <=> ! [X16,X18,X17,X19] : k2_enumset1(X16,X19,X18,X17) = k2_enumset1(X19,X17,X16,X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f123,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK3,sK1)
    | ~ spl4_4
    | spl4_5 ),
    inference(superposition,[],[f35,f28])).

fof(f28,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f35,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK0,sK1,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_5
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f122,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f84,f27,f19,f101])).

fof(f19,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( ! [X14,X12,X15,X13] : k2_enumset1(X12,X15,X14,X13) = k2_enumset1(X15,X13,X12,X14)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f20,f28])).

fof(f20,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f37,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f19,f14,f33])).

fof(f14,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK0,sK1,sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f16,f20])).

fof(f16,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f29,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

fof(f21,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f10,f19])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f17,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (741736448)
% 0.13/0.37  ipcrm: permission denied for id (744357890)
% 0.13/0.37  ipcrm: permission denied for id (741769219)
% 0.13/0.37  ipcrm: permission denied for id (741801988)
% 0.13/0.37  ipcrm: permission denied for id (744390661)
% 0.13/0.38  ipcrm: permission denied for id (741867526)
% 0.13/0.38  ipcrm: permission denied for id (744423431)
% 0.13/0.38  ipcrm: permission denied for id (744456200)
% 0.13/0.38  ipcrm: permission denied for id (741933065)
% 0.13/0.38  ipcrm: permission denied for id (744488970)
% 0.13/0.38  ipcrm: permission denied for id (741998603)
% 0.13/0.38  ipcrm: permission denied for id (744521740)
% 0.13/0.38  ipcrm: permission denied for id (744554509)
% 0.13/0.39  ipcrm: permission denied for id (742096911)
% 0.13/0.39  ipcrm: permission denied for id (747274256)
% 0.13/0.39  ipcrm: permission denied for id (742129682)
% 0.13/0.39  ipcrm: permission denied for id (744685587)
% 0.13/0.39  ipcrm: permission denied for id (742195220)
% 0.13/0.39  ipcrm: permission denied for id (742227989)
% 0.13/0.40  ipcrm: permission denied for id (744751127)
% 0.13/0.40  ipcrm: permission denied for id (742293528)
% 0.13/0.40  ipcrm: permission denied for id (744816666)
% 0.13/0.40  ipcrm: permission denied for id (747405339)
% 0.13/0.40  ipcrm: permission denied for id (742359068)
% 0.20/0.41  ipcrm: permission denied for id (744882205)
% 0.20/0.41  ipcrm: permission denied for id (747438110)
% 0.20/0.41  ipcrm: permission denied for id (742457377)
% 0.20/0.41  ipcrm: permission denied for id (747569187)
% 0.20/0.41  ipcrm: permission denied for id (742522916)
% 0.20/0.42  ipcrm: permission denied for id (745111590)
% 0.20/0.42  ipcrm: permission denied for id (745144359)
% 0.20/0.42  ipcrm: permission denied for id (745177128)
% 0.20/0.42  ipcrm: permission denied for id (747667497)
% 0.20/0.42  ipcrm: permission denied for id (747733035)
% 0.20/0.43  ipcrm: permission denied for id (747798573)
% 0.20/0.43  ipcrm: permission denied for id (742785070)
% 0.20/0.43  ipcrm: permission denied for id (745373743)
% 0.20/0.43  ipcrm: permission denied for id (745406512)
% 0.20/0.43  ipcrm: permission denied for id (742817841)
% 0.20/0.44  ipcrm: permission denied for id (745537589)
% 0.20/0.44  ipcrm: permission denied for id (745570358)
% 0.20/0.44  ipcrm: permission denied for id (745603127)
% 0.20/0.44  ipcrm: permission denied for id (745635896)
% 0.20/0.44  ipcrm: permission denied for id (745668665)
% 0.20/0.44  ipcrm: permission denied for id (745701434)
% 0.20/0.44  ipcrm: permission denied for id (745734203)
% 0.20/0.44  ipcrm: permission denied for id (743014460)
% 0.20/0.45  ipcrm: permission denied for id (745766973)
% 0.20/0.45  ipcrm: permission denied for id (743047230)
% 0.20/0.45  ipcrm: permission denied for id (743079999)
% 0.20/0.45  ipcrm: permission denied for id (747962432)
% 0.20/0.45  ipcrm: permission denied for id (743145538)
% 0.20/0.45  ipcrm: permission denied for id (743178307)
% 0.20/0.45  ipcrm: permission denied for id (743211076)
% 0.20/0.46  ipcrm: permission denied for id (743243845)
% 0.20/0.46  ipcrm: permission denied for id (745865286)
% 0.20/0.46  ipcrm: permission denied for id (745930824)
% 0.20/0.46  ipcrm: permission denied for id (743309385)
% 0.20/0.46  ipcrm: permission denied for id (743342155)
% 0.20/0.47  ipcrm: permission denied for id (743374925)
% 0.20/0.47  ipcrm: permission denied for id (748159054)
% 0.20/0.47  ipcrm: permission denied for id (748191823)
% 0.20/0.47  ipcrm: permission denied for id (746094672)
% 0.20/0.47  ipcrm: permission denied for id (746127441)
% 0.20/0.48  ipcrm: permission denied for id (748290132)
% 0.20/0.48  ipcrm: permission denied for id (746258517)
% 0.20/0.48  ipcrm: permission denied for id (743538775)
% 0.20/0.48  ipcrm: permission denied for id (746324056)
% 0.20/0.48  ipcrm: permission denied for id (746356825)
% 0.20/0.48  ipcrm: permission denied for id (748355674)
% 0.20/0.48  ipcrm: permission denied for id (746422363)
% 0.20/0.49  ipcrm: permission denied for id (748388444)
% 0.20/0.49  ipcrm: permission denied for id (748421213)
% 0.20/0.49  ipcrm: permission denied for id (748453982)
% 0.20/0.49  ipcrm: permission denied for id (743637087)
% 0.20/0.49  ipcrm: permission denied for id (743669856)
% 0.20/0.49  ipcrm: permission denied for id (748486753)
% 0.20/0.49  ipcrm: permission denied for id (746586210)
% 0.20/0.49  ipcrm: permission denied for id (746618979)
% 0.20/0.50  ipcrm: permission denied for id (743768164)
% 0.20/0.50  ipcrm: permission denied for id (746651749)
% 0.20/0.50  ipcrm: permission denied for id (748519526)
% 0.20/0.50  ipcrm: permission denied for id (748585064)
% 0.20/0.50  ipcrm: permission denied for id (748617833)
% 0.20/0.50  ipcrm: permission denied for id (743899242)
% 0.20/0.50  ipcrm: permission denied for id (746815595)
% 0.20/0.51  ipcrm: permission denied for id (743932012)
% 0.20/0.51  ipcrm: permission denied for id (746848365)
% 0.20/0.51  ipcrm: permission denied for id (746881134)
% 0.20/0.51  ipcrm: permission denied for id (748650607)
% 0.20/0.51  ipcrm: permission denied for id (746946672)
% 0.20/0.51  ipcrm: permission denied for id (746979441)
% 0.20/0.51  ipcrm: permission denied for id (744030322)
% 0.20/0.51  ipcrm: permission denied for id (744063091)
% 0.20/0.52  ipcrm: permission denied for id (744095860)
% 0.20/0.52  ipcrm: permission denied for id (744128629)
% 0.20/0.52  ipcrm: permission denied for id (747012214)
% 0.20/0.52  ipcrm: permission denied for id (744161399)
% 0.20/0.52  ipcrm: permission denied for id (744194168)
% 0.20/0.52  ipcrm: permission denied for id (748683385)
% 0.20/0.52  ipcrm: permission denied for id (744226938)
% 0.20/0.52  ipcrm: permission denied for id (744259707)
% 0.20/0.53  ipcrm: permission denied for id (747077756)
% 0.20/0.53  ipcrm: permission denied for id (747110525)
% 0.20/0.53  ipcrm: permission denied for id (748716158)
% 0.20/0.53  ipcrm: permission denied for id (747176063)
% 0.20/0.59  % (12333)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.59  % (12331)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.60  % (12323)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.81/0.60  % (12333)Refutation found. Thanks to Tanya!
% 0.81/0.60  % SZS status Theorem for theBenchmark
% 0.81/0.60  % SZS output start Proof for theBenchmark
% 0.81/0.60  fof(f140,plain,(
% 0.81/0.60    $false),
% 0.81/0.60    inference(avatar_sat_refutation,[],[f17,f21,f29,f37,f122,f128])).
% 0.81/0.60  fof(f128,plain,(
% 0.81/0.60    ~spl4_4 | spl4_5 | ~spl4_11),
% 0.81/0.60    inference(avatar_contradiction_clause,[],[f127])).
% 0.81/0.60  fof(f127,plain,(
% 0.81/0.60    $false | (~spl4_4 | spl4_5 | ~spl4_11)),
% 0.81/0.60    inference(subsumption_resolution,[],[f123,f102])).
% 0.81/0.60  fof(f102,plain,(
% 0.81/0.60    ( ! [X19,X17,X18,X16] : (k2_enumset1(X16,X19,X18,X17) = k2_enumset1(X19,X17,X16,X18)) ) | ~spl4_11),
% 0.81/0.60    inference(avatar_component_clause,[],[f101])).
% 0.81/0.60  fof(f101,plain,(
% 0.81/0.60    spl4_11 <=> ! [X16,X18,X17,X19] : k2_enumset1(X16,X19,X18,X17) = k2_enumset1(X19,X17,X16,X18)),
% 0.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.81/0.60  fof(f123,plain,(
% 0.81/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK3,sK1) | (~spl4_4 | spl4_5)),
% 0.81/0.60    inference(superposition,[],[f35,f28])).
% 0.81/0.60  fof(f28,plain,(
% 0.81/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)) ) | ~spl4_4),
% 0.81/0.60    inference(avatar_component_clause,[],[f27])).
% 0.81/0.60  fof(f27,plain,(
% 0.81/0.60    spl4_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.81/0.60  fof(f35,plain,(
% 0.81/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK0,sK1,sK2) | spl4_5),
% 0.81/0.60    inference(avatar_component_clause,[],[f33])).
% 0.81/0.60  fof(f33,plain,(
% 0.81/0.60    spl4_5 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK0,sK1,sK2)),
% 0.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.81/0.60  fof(f122,plain,(
% 0.81/0.60    spl4_11 | ~spl4_2 | ~spl4_4),
% 0.81/0.60    inference(avatar_split_clause,[],[f84,f27,f19,f101])).
% 0.81/0.60  fof(f19,plain,(
% 0.81/0.60    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.81/0.60  fof(f84,plain,(
% 0.81/0.60    ( ! [X14,X12,X15,X13] : (k2_enumset1(X12,X15,X14,X13) = k2_enumset1(X15,X13,X12,X14)) ) | (~spl4_2 | ~spl4_4)),
% 0.81/0.60    inference(superposition,[],[f20,f28])).
% 0.81/0.60  fof(f20,plain,(
% 0.81/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl4_2),
% 0.81/0.60    inference(avatar_component_clause,[],[f19])).
% 0.81/0.60  fof(f37,plain,(
% 0.81/0.60    ~spl4_5 | spl4_1 | ~spl4_2),
% 0.81/0.60    inference(avatar_split_clause,[],[f31,f19,f14,f33])).
% 0.81/0.60  fof(f14,plain,(
% 0.81/0.60    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.81/0.60  fof(f31,plain,(
% 0.81/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK0,sK1,sK2) | (spl4_1 | ~spl4_2)),
% 0.81/0.60    inference(superposition,[],[f16,f20])).
% 0.81/0.60  fof(f16,plain,(
% 0.81/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) | spl4_1),
% 0.81/0.60    inference(avatar_component_clause,[],[f14])).
% 0.81/0.60  fof(f29,plain,(
% 0.81/0.60    spl4_4),
% 0.81/0.60    inference(avatar_split_clause,[],[f12,f27])).
% 0.81/0.60  fof(f12,plain,(
% 0.81/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)) )),
% 0.81/0.60    inference(cnf_transformation,[],[f3])).
% 0.81/0.60  fof(f3,axiom,(
% 0.81/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
% 0.81/0.60  fof(f21,plain,(
% 0.81/0.60    spl4_2),
% 0.81/0.60    inference(avatar_split_clause,[],[f10,f19])).
% 0.81/0.60  fof(f10,plain,(
% 0.81/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.81/0.60    inference(cnf_transformation,[],[f1])).
% 0.81/0.60  fof(f1,axiom,(
% 0.81/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.81/0.61  fof(f17,plain,(
% 0.81/0.61    ~spl4_1),
% 0.81/0.61    inference(avatar_split_clause,[],[f9,f14])).
% 0.81/0.61  fof(f9,plain,(
% 0.81/0.61    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.81/0.61    inference(cnf_transformation,[],[f8])).
% 0.81/0.61  fof(f8,plain,(
% 0.81/0.61    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.81/0.61  fof(f7,plain,(
% 0.81/0.61    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.81/0.61    introduced(choice_axiom,[])).
% 0.81/0.61  fof(f6,plain,(
% 0.81/0.61    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.81/0.61    inference(ennf_transformation,[],[f5])).
% 0.81/0.61  fof(f5,negated_conjecture,(
% 0.81/0.61    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.81/0.61    inference(negated_conjecture,[],[f4])).
% 0.81/0.61  fof(f4,conjecture,(
% 0.81/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.81/0.61  % SZS output end Proof for theBenchmark
% 0.81/0.61  % (12333)------------------------------
% 0.81/0.61  % (12333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.81/0.61  % (12333)Termination reason: Refutation
% 0.81/0.61  
% 0.81/0.61  % (12333)Memory used [KB]: 6140
% 0.81/0.61  % (12333)Time elapsed: 0.028 s
% 0.81/0.61  % (12333)------------------------------
% 0.81/0.61  % (12333)------------------------------
% 0.81/0.61  % (12140)Success in time 0.246 s
%------------------------------------------------------------------------------
