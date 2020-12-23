%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:19 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 185 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f165,f176])).

fof(f176,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f126,f174])).

fof(f174,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f167,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f167,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_6 ),
    inference(superposition,[],[f40,f161])).

fof(f161,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_6
  <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f126,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f38,f123])).

fof(f123,plain,(
    ! [X8,X7] : k10_relat_1(k7_relat_1(sK0,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK0,X8)) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f38,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f165,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f157,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f157,plain,
    ( ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_5
  <=> v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f162,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f153,f159,f155])).

fof(f153,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f145,f83])).

fof(f83,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f145,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(k10_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(resolution,[],[f120,f37])).

fof(f37,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f119,f88])).

fof(f88,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f86,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f86,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X3)) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (789315584)
% 0.21/0.37  ipcrm: permission denied for id (791478274)
% 0.21/0.38  ipcrm: permission denied for id (791511043)
% 0.21/0.38  ipcrm: permission denied for id (791543812)
% 0.21/0.38  ipcrm: permission denied for id (791576581)
% 0.21/0.38  ipcrm: permission denied for id (789348358)
% 0.21/0.38  ipcrm: permission denied for id (789381127)
% 0.21/0.38  ipcrm: permission denied for id (791609352)
% 0.21/0.38  ipcrm: permission denied for id (791642121)
% 0.21/0.38  ipcrm: permission denied for id (794755082)
% 0.21/0.38  ipcrm: permission denied for id (791707659)
% 0.21/0.39  ipcrm: permission denied for id (789446668)
% 0.21/0.39  ipcrm: permission denied for id (794787853)
% 0.21/0.39  ipcrm: permission denied for id (791773198)
% 0.21/0.39  ipcrm: permission denied for id (794820623)
% 0.21/0.39  ipcrm: permission denied for id (791838736)
% 0.21/0.39  ipcrm: permission denied for id (794853393)
% 0.21/0.39  ipcrm: permission denied for id (789577746)
% 0.21/0.39  ipcrm: permission denied for id (789610515)
% 0.21/0.40  ipcrm: permission denied for id (791904276)
% 0.21/0.40  ipcrm: permission denied for id (791937045)
% 0.21/0.40  ipcrm: permission denied for id (794886166)
% 0.21/0.40  ipcrm: permission denied for id (792002583)
% 0.21/0.40  ipcrm: permission denied for id (792068121)
% 0.21/0.40  ipcrm: permission denied for id (792100890)
% 0.21/0.40  ipcrm: permission denied for id (794951707)
% 0.21/0.41  ipcrm: permission denied for id (792199197)
% 0.21/0.41  ipcrm: permission denied for id (792264735)
% 0.21/0.41  ipcrm: permission denied for id (792297504)
% 0.21/0.41  ipcrm: permission denied for id (789807137)
% 0.21/0.41  ipcrm: permission denied for id (789839906)
% 0.21/0.41  ipcrm: permission denied for id (789872675)
% 0.21/0.42  ipcrm: permission denied for id (795050020)
% 0.21/0.42  ipcrm: permission denied for id (792363045)
% 0.21/0.42  ipcrm: permission denied for id (792395814)
% 0.21/0.42  ipcrm: permission denied for id (792428583)
% 0.21/0.42  ipcrm: permission denied for id (795082792)
% 0.21/0.42  ipcrm: permission denied for id (792559659)
% 0.21/0.43  ipcrm: permission denied for id (792625197)
% 0.21/0.43  ipcrm: permission denied for id (795213870)
% 0.21/0.43  ipcrm: permission denied for id (795246639)
% 0.21/0.43  ipcrm: permission denied for id (792756272)
% 0.21/0.43  ipcrm: permission denied for id (792789041)
% 0.21/0.43  ipcrm: permission denied for id (792821810)
% 0.21/0.43  ipcrm: permission denied for id (792854579)
% 0.21/0.43  ipcrm: permission denied for id (795279412)
% 0.21/0.44  ipcrm: permission denied for id (795312181)
% 0.21/0.44  ipcrm: permission denied for id (790036535)
% 0.21/0.44  ipcrm: permission denied for id (792985656)
% 0.21/0.44  ipcrm: permission denied for id (790102073)
% 0.21/0.44  ipcrm: permission denied for id (793018426)
% 0.21/0.44  ipcrm: permission denied for id (790134843)
% 0.21/0.44  ipcrm: permission denied for id (795377724)
% 0.21/0.45  ipcrm: permission denied for id (793083965)
% 0.21/0.45  ipcrm: permission denied for id (793116734)
% 0.21/0.45  ipcrm: permission denied for id (793149503)
% 0.21/0.45  ipcrm: permission denied for id (795410496)
% 0.21/0.45  ipcrm: permission denied for id (793215041)
% 0.21/0.45  ipcrm: permission denied for id (793247810)
% 0.21/0.45  ipcrm: permission denied for id (795476036)
% 0.21/0.45  ipcrm: permission denied for id (793346117)
% 0.21/0.46  ipcrm: permission denied for id (793378886)
% 0.21/0.46  ipcrm: permission denied for id (795508807)
% 0.21/0.46  ipcrm: permission denied for id (793444424)
% 0.21/0.46  ipcrm: permission denied for id (793477193)
% 0.21/0.46  ipcrm: permission denied for id (790298698)
% 0.21/0.46  ipcrm: permission denied for id (795574348)
% 0.21/0.46  ipcrm: permission denied for id (790364237)
% 0.21/0.47  ipcrm: permission denied for id (795607118)
% 0.21/0.47  ipcrm: permission denied for id (793641039)
% 0.21/0.47  ipcrm: permission denied for id (795639888)
% 0.21/0.47  ipcrm: permission denied for id (793706577)
% 0.21/0.47  ipcrm: permission denied for id (790495314)
% 0.21/0.47  ipcrm: permission denied for id (790528083)
% 0.21/0.47  ipcrm: permission denied for id (790560852)
% 0.21/0.47  ipcrm: permission denied for id (790626389)
% 0.21/0.48  ipcrm: permission denied for id (793739350)
% 0.21/0.48  ipcrm: permission denied for id (795672663)
% 0.21/0.48  ipcrm: permission denied for id (793804888)
% 0.21/0.48  ipcrm: permission denied for id (790691929)
% 0.21/0.48  ipcrm: permission denied for id (795705434)
% 0.21/0.48  ipcrm: permission denied for id (790757467)
% 0.21/0.48  ipcrm: permission denied for id (793870428)
% 0.21/0.48  ipcrm: permission denied for id (790888542)
% 0.21/0.49  ipcrm: permission denied for id (790921311)
% 0.21/0.49  ipcrm: permission denied for id (793935968)
% 0.21/0.49  ipcrm: permission denied for id (790986851)
% 0.21/0.49  ipcrm: permission denied for id (791019620)
% 0.21/0.49  ipcrm: permission denied for id (791052389)
% 0.21/0.50  ipcrm: permission denied for id (791085159)
% 0.21/0.50  ipcrm: permission denied for id (794067048)
% 0.21/0.50  ipcrm: permission denied for id (795902058)
% 0.21/0.50  ipcrm: permission denied for id (791150699)
% 0.21/0.50  ipcrm: permission denied for id (794165356)
% 0.21/0.50  ipcrm: permission denied for id (791183469)
% 0.21/0.50  ipcrm: permission denied for id (794198126)
% 0.21/0.51  ipcrm: permission denied for id (795934831)
% 0.21/0.51  ipcrm: permission denied for id (791281777)
% 0.21/0.51  ipcrm: permission denied for id (794296434)
% 0.21/0.51  ipcrm: permission denied for id (796000371)
% 0.21/0.51  ipcrm: permission denied for id (796033140)
% 0.21/0.51  ipcrm: permission denied for id (794394741)
% 0.21/0.51  ipcrm: permission denied for id (796065910)
% 0.21/0.52  ipcrm: permission denied for id (791347319)
% 0.21/0.52  ipcrm: permission denied for id (794460280)
% 0.21/0.52  ipcrm: permission denied for id (794493049)
% 0.21/0.52  ipcrm: permission denied for id (794558587)
% 0.21/0.52  ipcrm: permission denied for id (796131452)
% 0.21/0.52  ipcrm: permission denied for id (794624125)
% 0.21/0.52  ipcrm: permission denied for id (794656894)
% 0.61/0.58  % (22758)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.61/0.61  % (22755)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.61/0.62  % (22748)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.61/0.62  % (22749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.61/0.63  % (22754)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.61/0.63  % (22760)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.61/0.64  % (22757)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.12/0.64  % (22746)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.12/0.64  % (22761)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.12/0.64  % (22751)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.12/0.65  % (22763)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.12/0.65  % (22747)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.12/0.65  % (22756)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.12/0.66  % (22750)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.12/0.66  % (22759)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.28/0.66  % (22753)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.28/0.66  % (22762)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.28/0.66  % (22752)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.28/0.67  % (22762)Refutation found. Thanks to Tanya!
% 1.28/0.67  % SZS status Theorem for theBenchmark
% 1.28/0.67  % SZS output start Proof for theBenchmark
% 1.28/0.67  fof(f183,plain,(
% 1.28/0.67    $false),
% 1.28/0.67    inference(avatar_sat_refutation,[],[f162,f165,f176])).
% 1.28/0.67  fof(f176,plain,(
% 1.28/0.67    ~spl3_6),
% 1.28/0.67    inference(avatar_contradiction_clause,[],[f175])).
% 1.28/0.67  fof(f175,plain,(
% 1.28/0.67    $false | ~spl3_6),
% 1.28/0.67    inference(subsumption_resolution,[],[f126,f174])).
% 1.28/0.67  fof(f174,plain,(
% 1.28/0.67    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl3_6),
% 1.28/0.67    inference(forward_demodulation,[],[f167,f40])).
% 1.28/0.67  fof(f40,plain,(
% 1.28/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.28/0.67    inference(cnf_transformation,[],[f12])).
% 1.28/0.67  fof(f12,axiom,(
% 1.28/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.28/0.67  fof(f167,plain,(
% 1.28/0.67    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_6),
% 1.28/0.67    inference(superposition,[],[f40,f161])).
% 1.28/0.67  fof(f161,plain,(
% 1.28/0.67    k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl3_6),
% 1.28/0.67    inference(avatar_component_clause,[],[f159])).
% 1.28/0.67  fof(f159,plain,(
% 1.28/0.67    spl3_6 <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 1.28/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.28/0.67  fof(f126,plain,(
% 1.28/0.67    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.28/0.67    inference(superposition,[],[f38,f123])).
% 1.28/0.67  fof(f123,plain,(
% 1.28/0.67    ( ! [X8,X7] : (k10_relat_1(k7_relat_1(sK0,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK0,X8))) )),
% 1.28/0.67    inference(resolution,[],[f52,f35])).
% 1.28/0.67  fof(f35,plain,(
% 1.28/0.67    v1_relat_1(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f34])).
% 1.28/0.67  fof(f34,plain,(
% 1.28/0.67    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f33,f32])).
% 1.28/0.68  fof(f32,plain,(
% 1.28/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.28/0.68    introduced(choice_axiom,[])).
% 1.28/0.68  fof(f33,plain,(
% 1.28/0.68    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.28/0.68    introduced(choice_axiom,[])).
% 1.28/0.68  fof(f22,plain,(
% 1.28/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.28/0.68    inference(flattening,[],[f21])).
% 1.28/0.68  fof(f21,plain,(
% 1.28/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.28/0.68    inference(ennf_transformation,[],[f20])).
% 1.28/0.68  fof(f20,negated_conjecture,(
% 1.28/0.68    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.28/0.68    inference(negated_conjecture,[],[f19])).
% 1.28/0.68  fof(f19,conjecture,(
% 1.28/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.28/0.68  fof(f52,plain,(
% 1.28/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.28/0.68    inference(cnf_transformation,[],[f29])).
% 1.28/0.68  fof(f29,plain,(
% 1.28/0.68    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.28/0.68    inference(ennf_transformation,[],[f17])).
% 1.28/0.68  fof(f17,axiom,(
% 1.28/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.28/0.68  fof(f38,plain,(
% 1.28/0.68    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.28/0.68    inference(cnf_transformation,[],[f34])).
% 1.28/0.68  fof(f165,plain,(
% 1.28/0.68    spl3_5),
% 1.28/0.68    inference(avatar_contradiction_clause,[],[f164])).
% 1.28/0.68  fof(f164,plain,(
% 1.28/0.68    $false | spl3_5),
% 1.28/0.68    inference(resolution,[],[f157,f39])).
% 1.28/0.68  fof(f39,plain,(
% 1.28/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.28/0.68    inference(cnf_transformation,[],[f10])).
% 1.28/0.68  fof(f10,axiom,(
% 1.28/0.68    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.28/0.68  fof(f157,plain,(
% 1.28/0.68    ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | spl3_5),
% 1.28/0.68    inference(avatar_component_clause,[],[f155])).
% 1.28/0.68  fof(f155,plain,(
% 1.28/0.68    spl3_5 <=> v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.28/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.28/0.68  fof(f162,plain,(
% 1.28/0.68    ~spl3_5 | spl3_6),
% 1.28/0.68    inference(avatar_split_clause,[],[f153,f159,f155])).
% 1.28/0.68  fof(f153,plain,(
% 1.28/0.68    k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.28/0.68    inference(forward_demodulation,[],[f145,f83])).
% 1.28/0.68  fof(f83,plain,(
% 1.28/0.68    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.28/0.68    inference(superposition,[],[f64,f45])).
% 1.28/0.68  fof(f45,plain,(
% 1.28/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.28/0.68    inference(cnf_transformation,[],[f9])).
% 1.28/0.68  fof(f9,axiom,(
% 1.28/0.68    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.28/0.68  fof(f64,plain,(
% 1.28/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.28/0.68    inference(superposition,[],[f45,f43])).
% 1.28/0.68  fof(f43,plain,(
% 1.28/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.28/0.68    inference(cnf_transformation,[],[f2])).
% 1.28/0.68  fof(f2,axiom,(
% 1.28/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.28/0.68  fof(f145,plain,(
% 1.28/0.68    k6_relat_1(k10_relat_1(sK0,sK2)) = k6_relat_1(k3_xboole_0(k10_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.28/0.68    inference(resolution,[],[f120,f37])).
% 1.28/0.68  fof(f37,plain,(
% 1.28/0.68    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.28/0.68    inference(cnf_transformation,[],[f34])).
% 1.28/0.68  fof(f120,plain,(
% 1.28/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.28/0.68    inference(forward_demodulation,[],[f119,f88])).
% 1.28/0.68  fof(f88,plain,(
% 1.28/0.68    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k3_xboole_0(X3,X4))) )),
% 1.28/0.68    inference(forward_demodulation,[],[f86,f46])).
% 1.28/0.68  fof(f46,plain,(
% 1.28/0.68    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.28/0.68    inference(cnf_transformation,[],[f18])).
% 1.28/0.68  fof(f18,axiom,(
% 1.28/0.68    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.28/0.68  fof(f86,plain,(
% 1.28/0.68    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X3))) )),
% 1.28/0.68    inference(resolution,[],[f49,f39])).
% 1.28/0.68  fof(f49,plain,(
% 1.28/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.28/0.68    inference(cnf_transformation,[],[f26])).
% 1.28/0.68  fof(f26,plain,(
% 1.28/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.28/0.68    inference(ennf_transformation,[],[f14])).
% 1.28/0.68  fof(f14,axiom,(
% 1.28/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.28/0.68  fof(f119,plain,(
% 1.28/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.28/0.68    inference(superposition,[],[f50,f40])).
% 1.28/0.68  fof(f50,plain,(
% 1.28/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.28/0.68    inference(cnf_transformation,[],[f28])).
% 1.28/0.68  fof(f28,plain,(
% 1.28/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.28/0.68    inference(flattening,[],[f27])).
% 1.28/0.68  fof(f27,plain,(
% 1.28/0.68    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.68    inference(ennf_transformation,[],[f15])).
% 1.28/0.68  fof(f15,axiom,(
% 1.28/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.28/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.28/0.68  % SZS output end Proof for theBenchmark
% 1.28/0.68  % (22762)------------------------------
% 1.28/0.68  % (22762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.68  % (22762)Termination reason: Refutation
% 1.28/0.68  
% 1.28/0.68  % (22762)Memory used [KB]: 6268
% 1.28/0.68  % (22762)Time elapsed: 0.060 s
% 1.28/0.68  % (22762)------------------------------
% 1.28/0.68  % (22762)------------------------------
% 1.28/0.68  % (22612)Success in time 0.315 s
%------------------------------------------------------------------------------
