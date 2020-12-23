%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 5.60s
% Output     : Refutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 147 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 165 expanded)
%              Number of equality atoms :   44 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f2648,f2649,f4092])).

fof(f4092,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f4091])).

fof(f4091,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2647,f3948])).

fof(f3948,plain,(
    ! [X269,X271,X268,X270,X272] : k2_enumset1(k4_tarski(k4_tarski(X268,X269),X271),k4_tarski(k4_tarski(X268,X269),X272),k4_tarski(k4_tarski(X268,X270),X271),k4_tarski(k4_tarski(X268,X270),X272)) = k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X268),k2_enumset1(X269,X269,X269,X270)),k2_enumset1(X271,X271,X271,X272)) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f25,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f2647,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f2645])).

fof(f2645,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2649,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2643,f41,f2645])).

fof(f41,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2643,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_1 ),
    inference(superposition,[],[f43,f2491])).

fof(f2491,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(superposition,[],[f596,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X1,X2,X3)) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f596,plain,(
    ! [X28,X26,X29,X27] : k2_enumset1(X29,X26,X27,X28) = k2_xboole_0(k1_tarski(X29),k2_enumset1(X27,X27,X26,X28)) ),
    inference(forward_demodulation,[],[f589,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f589,plain,(
    ! [X28,X26,X29,X27] : k2_enumset1(X29,X26,X27,X28) = k2_xboole_0(k1_tarski(X29),k2_xboole_0(k2_enumset1(X27,X27,X27,X26),k1_tarski(X28))) ),
    inference(superposition,[],[f33,f111])).

fof(f111,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k2_enumset1(X3,X3,X3,X2),k1_tarski(X4)) = k2_enumset1(X2,X2,X3,X4) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f19,f30,f30])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f43,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f2648,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2604,f41,f2645])).

fof(f2604,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_1 ),
    inference(superposition,[],[f43,f2491])).

fof(f44,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f34,f41])).

fof(f34,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f17,f22,f30,f30,f24,f24,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:10 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1217822720)
% 0.21/0.37  ipcrm: permission denied for id (1224409089)
% 0.21/0.37  ipcrm: permission denied for id (1217888258)
% 0.21/0.37  ipcrm: permission denied for id (1222082564)
% 0.21/0.37  ipcrm: permission denied for id (1222115333)
% 0.21/0.37  ipcrm: permission denied for id (1217986566)
% 0.21/0.37  ipcrm: permission denied for id (1218019335)
% 0.21/0.38  ipcrm: permission denied for id (1226211336)
% 0.21/0.38  ipcrm: permission denied for id (1224507401)
% 0.21/0.38  ipcrm: permission denied for id (1224540170)
% 0.21/0.38  ipcrm: permission denied for id (1222246411)
% 0.21/0.38  ipcrm: permission denied for id (1222279180)
% 0.21/0.38  ipcrm: permission denied for id (1218150413)
% 0.21/0.38  ipcrm: permission denied for id (1218183182)
% 0.21/0.38  ipcrm: permission denied for id (1222311951)
% 0.21/0.39  ipcrm: permission denied for id (1218248720)
% 0.21/0.39  ipcrm: permission denied for id (1218281489)
% 0.21/0.39  ipcrm: permission denied for id (1222344722)
% 0.21/0.39  ipcrm: permission denied for id (1218347027)
% 0.21/0.39  ipcrm: permission denied for id (1222377492)
% 0.21/0.39  ipcrm: permission denied for id (1224572949)
% 0.21/0.39  ipcrm: permission denied for id (1218445334)
% 0.21/0.39  ipcrm: permission denied for id (1218478103)
% 0.21/0.40  ipcrm: permission denied for id (1218510872)
% 0.21/0.40  ipcrm: permission denied for id (1222443033)
% 0.21/0.40  ipcrm: permission denied for id (1218576410)
% 0.21/0.40  ipcrm: permission denied for id (1218609179)
% 0.21/0.40  ipcrm: permission denied for id (1218641948)
% 0.21/0.40  ipcrm: permission denied for id (1218674717)
% 0.21/0.40  ipcrm: permission denied for id (1225687070)
% 0.21/0.40  ipcrm: permission denied for id (1224638495)
% 0.21/0.41  ipcrm: permission denied for id (1222541344)
% 0.21/0.41  ipcrm: permission denied for id (1225719841)
% 0.21/0.41  ipcrm: permission denied for id (1222606882)
% 0.21/0.41  ipcrm: permission denied for id (1218871331)
% 0.21/0.41  ipcrm: permission denied for id (1222639652)
% 0.21/0.41  ipcrm: permission denied for id (1226244133)
% 0.21/0.41  ipcrm: permission denied for id (1218969638)
% 0.21/0.41  ipcrm: permission denied for id (1222705191)
% 0.21/0.42  ipcrm: permission denied for id (1219067944)
% 0.21/0.42  ipcrm: permission denied for id (1219100713)
% 0.21/0.42  ipcrm: permission denied for id (1222737962)
% 0.21/0.42  ipcrm: permission denied for id (1225785387)
% 0.21/0.42  ipcrm: permission denied for id (1219231788)
% 0.21/0.42  ipcrm: permission denied for id (1219264557)
% 0.21/0.42  ipcrm: permission denied for id (1224769582)
% 0.21/0.43  ipcrm: permission denied for id (1224802351)
% 0.21/0.43  ipcrm: permission denied for id (1224835120)
% 0.21/0.43  ipcrm: permission denied for id (1219395633)
% 0.21/0.43  ipcrm: permission denied for id (1219428402)
% 0.21/0.43  ipcrm: permission denied for id (1222934579)
% 0.21/0.43  ipcrm: permission denied for id (1222967348)
% 0.21/0.43  ipcrm: permission denied for id (1223000117)
% 0.21/0.43  ipcrm: permission denied for id (1224867894)
% 0.21/0.44  ipcrm: permission denied for id (1223065655)
% 0.21/0.44  ipcrm: permission denied for id (1223098424)
% 0.21/0.44  ipcrm: permission denied for id (1223131193)
% 0.21/0.44  ipcrm: permission denied for id (1219690554)
% 0.21/0.44  ipcrm: permission denied for id (1219723323)
% 0.21/0.44  ipcrm: permission denied for id (1219756092)
% 0.21/0.44  ipcrm: permission denied for id (1223163965)
% 0.21/0.45  ipcrm: permission denied for id (1225850943)
% 0.21/0.45  ipcrm: permission denied for id (1219887168)
% 0.21/0.45  ipcrm: permission denied for id (1219952705)
% 0.21/0.45  ipcrm: permission denied for id (1223262274)
% 0.21/0.45  ipcrm: permission denied for id (1223295043)
% 0.21/0.45  ipcrm: permission denied for id (1220051012)
% 0.21/0.45  ipcrm: permission denied for id (1224966213)
% 0.21/0.45  ipcrm: permission denied for id (1220116550)
% 0.21/0.46  ipcrm: permission denied for id (1225883719)
% 0.21/0.46  ipcrm: permission denied for id (1220182088)
% 0.21/0.46  ipcrm: permission denied for id (1220214857)
% 0.21/0.46  ipcrm: permission denied for id (1225916490)
% 0.21/0.46  ipcrm: permission denied for id (1225064523)
% 0.21/0.46  ipcrm: permission denied for id (1220313164)
% 0.21/0.46  ipcrm: permission denied for id (1225097293)
% 0.21/0.46  ipcrm: permission denied for id (1223491662)
% 0.21/0.47  ipcrm: permission denied for id (1220411471)
% 0.21/0.47  ipcrm: permission denied for id (1223524432)
% 0.21/0.47  ipcrm: permission denied for id (1225130065)
% 0.21/0.47  ipcrm: permission denied for id (1220509778)
% 0.21/0.47  ipcrm: permission denied for id (1220542547)
% 0.21/0.47  ipcrm: permission denied for id (1223589972)
% 0.21/0.47  ipcrm: permission denied for id (1220608085)
% 0.21/0.47  ipcrm: permission denied for id (1220640854)
% 0.21/0.48  ipcrm: permission denied for id (1223622743)
% 0.21/0.48  ipcrm: permission denied for id (1225982041)
% 0.21/0.48  ipcrm: permission denied for id (1220771930)
% 0.21/0.48  ipcrm: permission denied for id (1220804699)
% 0.21/0.48  ipcrm: permission denied for id (1220837468)
% 0.21/0.48  ipcrm: permission denied for id (1225228381)
% 0.21/0.48  ipcrm: permission denied for id (1220903006)
% 0.21/0.49  ipcrm: permission denied for id (1223753823)
% 0.21/0.49  ipcrm: permission denied for id (1220968544)
% 0.21/0.49  ipcrm: permission denied for id (1221001313)
% 0.21/0.49  ipcrm: permission denied for id (1226014818)
% 0.21/0.49  ipcrm: permission denied for id (1221066851)
% 0.21/0.49  ipcrm: permission denied for id (1225326693)
% 0.21/0.49  ipcrm: permission denied for id (1221165158)
% 0.21/0.50  ipcrm: permission denied for id (1221197927)
% 0.21/0.50  ipcrm: permission denied for id (1221230696)
% 0.21/0.50  ipcrm: permission denied for id (1221263465)
% 0.21/0.50  ipcrm: permission denied for id (1223884906)
% 0.21/0.50  ipcrm: permission denied for id (1225359467)
% 0.21/0.50  ipcrm: permission denied for id (1221361772)
% 0.21/0.50  ipcrm: permission denied for id (1221394541)
% 0.21/0.50  ipcrm: permission denied for id (1223950446)
% 0.21/0.51  ipcrm: permission denied for id (1223983215)
% 0.21/0.51  ipcrm: permission denied for id (1225392240)
% 0.21/0.51  ipcrm: permission denied for id (1221492849)
% 0.21/0.51  ipcrm: permission denied for id (1226375282)
% 0.21/0.51  ipcrm: permission denied for id (1221591156)
% 0.21/0.51  ipcrm: permission denied for id (1221623925)
% 0.21/0.51  ipcrm: permission denied for id (1224114294)
% 0.21/0.52  ipcrm: permission denied for id (1225490551)
% 0.21/0.52  ipcrm: permission denied for id (1221722232)
% 0.21/0.52  ipcrm: permission denied for id (1224212601)
% 0.21/0.52  ipcrm: permission denied for id (1226145914)
% 0.21/0.52  ipcrm: permission denied for id (1225588859)
% 0.21/0.52  ipcrm: permission denied for id (1224310908)
% 0.21/0.52  ipcrm: permission denied for id (1224343677)
% 0.21/0.52  ipcrm: permission denied for id (1224376446)
% 0.21/0.52  ipcrm: permission denied for id (1221984383)
% 0.51/0.59  % (5280)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.74/0.61  % (5271)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.74/0.63  % (5278)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.74/0.63  % (5267)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.74/0.63  % (5278)Refutation not found, incomplete strategy% (5278)------------------------------
% 0.74/0.63  % (5278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.74/0.63  % (5278)Termination reason: Refutation not found, incomplete strategy
% 0.74/0.63  
% 0.74/0.64  % (5278)Memory used [KB]: 10618
% 0.74/0.64  % (5278)Time elapsed: 0.075 s
% 0.74/0.64  % (5278)------------------------------
% 0.74/0.64  % (5278)------------------------------
% 1.21/0.66  % (5279)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.21/0.67  % (5274)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.21/0.67  % (5276)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.21/0.68  % (5275)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.21/0.69  % (5268)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.21/0.69  % (5270)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.21/0.69  % (5269)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.21/0.69  % (5272)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.21/0.69  % (5277)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.21/0.70  % (5282)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.21/0.70  % (5281)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.59/0.70  % (5283)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.59/0.71  % (5273)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.59/0.71  % (5284)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.21/1.18  % (5271)Time limit reached!
% 5.21/1.18  % (5271)------------------------------
% 5.21/1.18  % (5271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.18  % (5271)Termination reason: Time limit
% 5.21/1.18  % (5271)Termination phase: Saturation
% 5.21/1.18  
% 5.21/1.18  % (5271)Memory used [KB]: 11129
% 5.21/1.18  % (5271)Time elapsed: 0.600 s
% 5.21/1.18  % (5271)------------------------------
% 5.21/1.18  % (5271)------------------------------
% 5.60/1.23  % (5277)Refutation found. Thanks to Tanya!
% 5.60/1.23  % SZS status Theorem for theBenchmark
% 5.60/1.23  % SZS output start Proof for theBenchmark
% 5.60/1.23  fof(f4182,plain,(
% 5.60/1.23    $false),
% 5.60/1.23    inference(avatar_sat_refutation,[],[f44,f2648,f2649,f4092])).
% 5.60/1.23  fof(f4092,plain,(
% 5.60/1.23    spl5_2),
% 5.60/1.23    inference(avatar_contradiction_clause,[],[f4091])).
% 5.60/1.23  fof(f4091,plain,(
% 5.60/1.23    $false | spl5_2),
% 5.60/1.23    inference(subsumption_resolution,[],[f2647,f3948])).
% 5.60/1.23  fof(f3948,plain,(
% 5.60/1.23    ( ! [X269,X271,X268,X270,X272] : (k2_enumset1(k4_tarski(k4_tarski(X268,X269),X271),k4_tarski(k4_tarski(X268,X269),X272),k4_tarski(k4_tarski(X268,X270),X271),k4_tarski(k4_tarski(X268,X270),X272)) = k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X268),k2_enumset1(X269,X269,X269,X270)),k2_enumset1(X271,X271,X271,X272))) )),
% 5.60/1.23    inference(superposition,[],[f39,f37])).
% 5.60/1.23  fof(f37,plain,(
% 5.60/1.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 5.60/1.23    inference(definition_unfolding,[],[f25,f30,f30])).
% 5.60/1.23  fof(f30,plain,(
% 5.60/1.23    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 5.60/1.23    inference(definition_unfolding,[],[f20,f23])).
% 5.60/1.23  fof(f23,plain,(
% 5.60/1.23    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 5.60/1.23    inference(cnf_transformation,[],[f6])).
% 5.60/1.23  fof(f6,axiom,(
% 5.60/1.23    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 5.60/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 5.60/1.23  fof(f20,plain,(
% 5.60/1.23    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 5.60/1.23    inference(cnf_transformation,[],[f5])).
% 5.60/1.23  fof(f5,axiom,(
% 5.60/1.23    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 5.60/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.60/1.23  fof(f25,plain,(
% 5.60/1.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 5.60/1.23    inference(cnf_transformation,[],[f9])).
% 5.60/1.23  fof(f9,axiom,(
% 5.60/1.23    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 5.60/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 5.60/1.23  fof(f39,plain,(
% 5.60/1.23    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 5.60/1.23    inference(definition_unfolding,[],[f29,f30,f30])).
% 5.60/1.23  fof(f29,plain,(
% 5.60/1.23    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 5.60/1.23    inference(cnf_transformation,[],[f8])).
% 5.60/1.23  fof(f8,axiom,(
% 5.60/1.23    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 5.60/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 5.60/1.23  fof(f2647,plain,(
% 5.60/1.23    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_2),
% 5.60/1.23    inference(avatar_component_clause,[],[f2645])).
% 5.60/1.24  fof(f2645,plain,(
% 5.60/1.24    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 5.60/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 5.60/1.24  fof(f2649,plain,(
% 5.60/1.24    ~spl5_2 | spl5_1),
% 5.60/1.24    inference(avatar_split_clause,[],[f2643,f41,f2645])).
% 5.60/1.24  fof(f41,plain,(
% 5.60/1.24    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 5.60/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 5.60/1.24  fof(f2643,plain,(
% 5.60/1.24    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_1),
% 5.60/1.24    inference(superposition,[],[f43,f2491])).
% 5.60/1.24  fof(f2491,plain,(
% 5.60/1.24    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 5.60/1.24    inference(superposition,[],[f596,f33])).
% 5.60/1.24  fof(f33,plain,(
% 5.60/1.24    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X1,X2,X3))) )),
% 5.60/1.24    inference(definition_unfolding,[],[f27,f23])).
% 5.60/1.24  fof(f27,plain,(
% 5.60/1.24    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 5.60/1.24    inference(cnf_transformation,[],[f2])).
% 5.60/1.24  fof(f2,axiom,(
% 5.60/1.24    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 5.60/1.24  fof(f596,plain,(
% 5.60/1.24    ( ! [X28,X26,X29,X27] : (k2_enumset1(X29,X26,X27,X28) = k2_xboole_0(k1_tarski(X29),k2_enumset1(X27,X27,X26,X28))) )),
% 5.60/1.24    inference(forward_demodulation,[],[f589,f38])).
% 5.60/1.24  fof(f38,plain,(
% 5.60/1.24    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_tarski(X3))) )),
% 5.60/1.24    inference(definition_unfolding,[],[f28,f23])).
% 5.60/1.24  fof(f28,plain,(
% 5.60/1.24    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 5.60/1.24    inference(cnf_transformation,[],[f3])).
% 5.60/1.24  fof(f3,axiom,(
% 5.60/1.24    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 5.60/1.24  fof(f589,plain,(
% 5.60/1.24    ( ! [X28,X26,X29,X27] : (k2_enumset1(X29,X26,X27,X28) = k2_xboole_0(k1_tarski(X29),k2_xboole_0(k2_enumset1(X27,X27,X27,X26),k1_tarski(X28)))) )),
% 5.60/1.24    inference(superposition,[],[f33,f111])).
% 5.60/1.24  fof(f111,plain,(
% 5.60/1.24    ( ! [X4,X2,X3] : (k2_xboole_0(k2_enumset1(X3,X3,X3,X2),k1_tarski(X4)) = k2_enumset1(X2,X2,X3,X4)) )),
% 5.60/1.24    inference(superposition,[],[f38,f35])).
% 5.60/1.24  fof(f35,plain,(
% 5.60/1.24    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 5.60/1.24    inference(definition_unfolding,[],[f19,f30,f30])).
% 5.60/1.24  fof(f19,plain,(
% 5.60/1.24    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 5.60/1.24    inference(cnf_transformation,[],[f1])).
% 5.60/1.24  fof(f1,axiom,(
% 5.60/1.24    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 5.60/1.24  fof(f43,plain,(
% 5.60/1.24    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_1),
% 5.60/1.24    inference(avatar_component_clause,[],[f41])).
% 5.60/1.24  fof(f2648,plain,(
% 5.60/1.24    ~spl5_2 | spl5_1),
% 5.60/1.24    inference(avatar_split_clause,[],[f2604,f41,f2645])).
% 5.60/1.24  fof(f2604,plain,(
% 5.60/1.24    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_1),
% 5.60/1.24    inference(superposition,[],[f43,f2491])).
% 5.60/1.24  fof(f44,plain,(
% 5.60/1.24    ~spl5_1),
% 5.60/1.24    inference(avatar_split_clause,[],[f34,f41])).
% 5.60/1.24  fof(f34,plain,(
% 5.60/1.24    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 5.60/1.24    inference(definition_unfolding,[],[f17,f22,f30,f30,f24,f24,f24,f24])).
% 5.60/1.24  fof(f24,plain,(
% 5.60/1.24    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 5.60/1.24    inference(cnf_transformation,[],[f10])).
% 5.60/1.24  fof(f10,axiom,(
% 5.60/1.24    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 5.60/1.24  fof(f22,plain,(
% 5.60/1.24    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 5.60/1.24    inference(cnf_transformation,[],[f11])).
% 5.60/1.24  fof(f11,axiom,(
% 5.60/1.24    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 5.60/1.24  fof(f17,plain,(
% 5.60/1.24    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 5.60/1.24    inference(cnf_transformation,[],[f16])).
% 5.60/1.24  fof(f16,plain,(
% 5.60/1.24    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 5.60/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f15])).
% 5.60/1.24  fof(f15,plain,(
% 5.60/1.24    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 5.60/1.24    introduced(choice_axiom,[])).
% 5.60/1.24  fof(f14,plain,(
% 5.60/1.24    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 5.60/1.24    inference(ennf_transformation,[],[f13])).
% 5.60/1.24  fof(f13,negated_conjecture,(
% 5.60/1.24    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 5.60/1.24    inference(negated_conjecture,[],[f12])).
% 5.60/1.24  fof(f12,conjecture,(
% 5.60/1.24    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 5.60/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 5.60/1.24  % SZS output end Proof for theBenchmark
% 5.60/1.24  % (5277)------------------------------
% 5.60/1.24  % (5277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.24  % (5277)Termination reason: Refutation
% 5.60/1.24  
% 5.60/1.24  % (5277)Memory used [KB]: 9338
% 5.60/1.24  % (5277)Time elapsed: 0.599 s
% 5.60/1.24  % (5277)------------------------------
% 5.60/1.24  % (5277)------------------------------
% 5.88/1.25  % (5128)Success in time 0.876 s
%------------------------------------------------------------------------------
