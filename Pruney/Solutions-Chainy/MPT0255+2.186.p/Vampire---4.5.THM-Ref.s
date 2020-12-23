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
% DateTime   : Thu Dec  3 12:39:58 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 236 expanded)
%              Number of leaves         :   14 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :   57 ( 243 expanded)
%              Number of equality atoms :   56 ( 242 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f73,f50])).

fof(f50,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(backward_demodulation,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f25,f35,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f39,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f19,f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f36])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f30,f32,f37,f38,f33])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f36])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f21,f37,f38])).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:48:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.38  ipcrm: permission denied for id (805502976)
% 0.15/0.38  ipcrm: permission denied for id (805863425)
% 0.15/0.38  ipcrm: permission denied for id (805994501)
% 0.15/0.38  ipcrm: permission denied for id (806027270)
% 0.15/0.39  ipcrm: permission denied for id (806125576)
% 0.15/0.39  ipcrm: permission denied for id (810156041)
% 0.15/0.39  ipcrm: permission denied for id (805535755)
% 0.15/0.39  ipcrm: permission denied for id (806223884)
% 0.15/0.39  ipcrm: permission denied for id (806256653)
% 0.15/0.39  ipcrm: permission denied for id (806289422)
% 0.15/0.40  ipcrm: permission denied for id (810221583)
% 0.15/0.40  ipcrm: permission denied for id (806354960)
% 0.15/0.40  ipcrm: permission denied for id (810254353)
% 0.15/0.40  ipcrm: permission denied for id (806420498)
% 0.15/0.40  ipcrm: permission denied for id (810287123)
% 0.15/0.40  ipcrm: permission denied for id (806551574)
% 0.15/0.40  ipcrm: permission denied for id (806584343)
% 0.15/0.41  ipcrm: permission denied for id (806617112)
% 0.15/0.41  ipcrm: permission denied for id (806682650)
% 0.15/0.41  ipcrm: permission denied for id (806715419)
% 0.15/0.41  ipcrm: permission denied for id (806748188)
% 0.15/0.41  ipcrm: permission denied for id (805634077)
% 0.15/0.41  ipcrm: permission denied for id (806780958)
% 0.15/0.41  ipcrm: permission denied for id (806813727)
% 0.15/0.42  ipcrm: permission denied for id (806846496)
% 0.15/0.42  ipcrm: permission denied for id (806879265)
% 0.15/0.42  ipcrm: permission denied for id (810418210)
% 0.15/0.42  ipcrm: permission denied for id (810450979)
% 0.15/0.42  ipcrm: permission denied for id (807043110)
% 0.15/0.42  ipcrm: permission denied for id (807075879)
% 0.22/0.43  ipcrm: permission denied for id (807141416)
% 0.22/0.43  ipcrm: permission denied for id (810549289)
% 0.22/0.43  ipcrm: permission denied for id (807206954)
% 0.22/0.43  ipcrm: permission denied for id (807272492)
% 0.22/0.43  ipcrm: permission denied for id (807305261)
% 0.22/0.43  ipcrm: permission denied for id (810614830)
% 0.22/0.43  ipcrm: permission denied for id (807370799)
% 0.22/0.44  ipcrm: permission denied for id (807469106)
% 0.22/0.44  ipcrm: permission denied for id (810713139)
% 0.22/0.44  ipcrm: permission denied for id (810745908)
% 0.22/0.44  ipcrm: permission denied for id (807567413)
% 0.22/0.45  ipcrm: permission denied for id (807665720)
% 0.22/0.45  ipcrm: permission denied for id (810876985)
% 0.22/0.45  ipcrm: permission denied for id (807731258)
% 0.22/0.45  ipcrm: permission denied for id (807764027)
% 0.22/0.45  ipcrm: permission denied for id (807796796)
% 0.22/0.45  ipcrm: permission denied for id (807829565)
% 0.22/0.46  ipcrm: permission denied for id (807895103)
% 0.22/0.46  ipcrm: permission denied for id (807927872)
% 0.22/0.46  ipcrm: permission denied for id (807960641)
% 0.22/0.46  ipcrm: permission denied for id (807993410)
% 0.22/0.46  ipcrm: permission denied for id (810942531)
% 0.22/0.46  ipcrm: permission denied for id (808058948)
% 0.22/0.47  ipcrm: permission denied for id (808157254)
% 0.22/0.47  ipcrm: permission denied for id (808190023)
% 0.22/0.47  ipcrm: permission denied for id (811008072)
% 0.22/0.47  ipcrm: permission denied for id (811073610)
% 0.22/0.47  ipcrm: permission denied for id (808321099)
% 0.22/0.47  ipcrm: permission denied for id (811139149)
% 0.22/0.48  ipcrm: permission denied for id (811171918)
% 0.22/0.48  ipcrm: permission denied for id (808452175)
% 0.22/0.48  ipcrm: permission denied for id (811237457)
% 0.22/0.48  ipcrm: permission denied for id (808550482)
% 0.22/0.48  ipcrm: permission denied for id (808583251)
% 0.22/0.48  ipcrm: permission denied for id (811270228)
% 0.22/0.49  ipcrm: permission denied for id (811302997)
% 0.22/0.49  ipcrm: permission denied for id (808681558)
% 0.22/0.49  ipcrm: permission denied for id (805732439)
% 0.22/0.49  ipcrm: permission denied for id (811335768)
% 0.22/0.49  ipcrm: permission denied for id (808747097)
% 0.22/0.49  ipcrm: permission denied for id (808812635)
% 0.22/0.49  ipcrm: permission denied for id (805765212)
% 0.22/0.50  ipcrm: permission denied for id (808845405)
% 0.22/0.50  ipcrm: permission denied for id (808878174)
% 0.22/0.50  ipcrm: permission denied for id (808910943)
% 0.22/0.50  ipcrm: permission denied for id (811466850)
% 0.22/0.50  ipcrm: permission denied for id (811499619)
% 0.22/0.51  ipcrm: permission denied for id (809074788)
% 0.22/0.51  ipcrm: permission denied for id (809107557)
% 0.22/0.51  ipcrm: permission denied for id (805797990)
% 0.22/0.51  ipcrm: permission denied for id (809140327)
% 0.22/0.51  ipcrm: permission denied for id (811532392)
% 0.22/0.51  ipcrm: permission denied for id (811565161)
% 0.22/0.51  ipcrm: permission denied for id (809238634)
% 0.22/0.51  ipcrm: permission denied for id (809271403)
% 0.22/0.52  ipcrm: permission denied for id (809304172)
% 0.22/0.52  ipcrm: permission denied for id (811663471)
% 0.22/0.52  ipcrm: permission denied for id (809500785)
% 0.22/0.52  ipcrm: permission denied for id (811729010)
% 0.22/0.52  ipcrm: permission denied for id (809566323)
% 0.22/0.53  ipcrm: permission denied for id (811761780)
% 0.22/0.53  ipcrm: permission denied for id (809697399)
% 0.22/0.53  ipcrm: permission denied for id (809730168)
% 0.22/0.53  ipcrm: permission denied for id (809795706)
% 0.22/0.53  ipcrm: permission denied for id (809828475)
% 0.22/0.54  ipcrm: permission denied for id (809861244)
% 0.22/0.54  ipcrm: permission denied for id (811925630)
% 0.22/0.54  ipcrm: permission denied for id (811958399)
% 0.39/0.61  % (21461)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.39/0.61  % (21460)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.39/0.62  % (21461)Refutation found. Thanks to Tanya!
% 0.39/0.62  % SZS status Theorem for theBenchmark
% 0.39/0.62  % SZS output start Proof for theBenchmark
% 0.39/0.62  fof(f81,plain,(
% 0.39/0.62    $false),
% 0.39/0.62    inference(trivial_inequality_removal,[],[f80])).
% 0.39/0.62  fof(f80,plain,(
% 0.39/0.62    k1_xboole_0 != k1_xboole_0),
% 0.39/0.62    inference(superposition,[],[f73,f50])).
% 0.39/0.62  fof(f50,plain,(
% 0.39/0.62    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.39/0.62    inference(trivial_inequality_removal,[],[f49])).
% 0.39/0.62  fof(f49,plain,(
% 0.39/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.39/0.62    inference(superposition,[],[f45,f44])).
% 0.39/0.62  fof(f44,plain,(
% 0.39/0.62    k1_xboole_0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.39/0.62    inference(backward_demodulation,[],[f39,f42])).
% 0.39/0.62  fof(f42,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f25,f35,f35])).
% 0.39/0.62  fof(f35,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f26,f34])).
% 0.39/0.62  fof(f34,plain,(
% 0.39/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f27,f33])).
% 0.39/0.62  fof(f33,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f28,f32])).
% 0.39/0.62  fof(f32,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f29,f31])).
% 0.39/0.62  fof(f31,plain,(
% 0.39/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f10])).
% 0.39/0.62  fof(f10,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.39/0.62  fof(f29,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f9])).
% 0.39/0.62  fof(f9,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.39/0.62  fof(f28,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f8])).
% 0.39/0.62  fof(f8,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.39/0.62  fof(f27,plain,(
% 0.39/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f7])).
% 0.39/0.62  fof(f7,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.39/0.62  fof(f26,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f6])).
% 0.39/0.62  fof(f6,axiom,(
% 0.39/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.39/0.62  fof(f25,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f2])).
% 0.39/0.62  fof(f2,axiom,(
% 0.39/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 0.39/0.62  fof(f39,plain,(
% 0.39/0.62    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.39/0.62    inference(definition_unfolding,[],[f19,f37,f36])).
% 0.39/0.62  fof(f36,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f23,f35])).
% 0.39/0.62  fof(f23,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f5])).
% 0.39/0.62  fof(f5,axiom,(
% 0.39/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.39/0.62  fof(f37,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f22,f36])).
% 0.39/0.62  fof(f22,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f11])).
% 0.39/0.62  fof(f11,axiom,(
% 0.39/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.39/0.62  fof(f19,plain,(
% 0.39/0.62    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.39/0.62    inference(cnf_transformation,[],[f18])).
% 0.39/0.62  fof(f18,plain,(
% 0.39/0.62    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.39/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.39/0.62  fof(f17,plain,(
% 0.39/0.62    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.39/0.62    introduced(choice_axiom,[])).
% 0.39/0.62  fof(f15,plain,(
% 0.39/0.62    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.39/0.62    inference(ennf_transformation,[],[f14])).
% 0.39/0.62  fof(f14,negated_conjecture,(
% 0.39/0.62    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.39/0.62    inference(negated_conjecture,[],[f13])).
% 0.39/0.62  fof(f13,conjecture,(
% 0.39/0.62    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.39/0.62  fof(f45,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0)) | k1_xboole_0 = X0) )),
% 0.39/0.62    inference(superposition,[],[f41,f42])).
% 0.39/0.62  fof(f41,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | k1_xboole_0 = X0) )),
% 0.39/0.62    inference(definition_unfolding,[],[f24,f37])).
% 0.39/0.62  fof(f24,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.39/0.62    inference(cnf_transformation,[],[f16])).
% 0.39/0.62  fof(f16,plain,(
% 0.39/0.62    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.39/0.62    inference(ennf_transformation,[],[f1])).
% 0.39/0.62  fof(f1,axiom,(
% 0.39/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.39/0.62  fof(f73,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.39/0.62    inference(superposition,[],[f40,f43])).
% 0.39/0.62  fof(f43,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f30,f32,f37,f38,f33])).
% 0.39/0.62  fof(f38,plain,(
% 0.39/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.39/0.62    inference(definition_unfolding,[],[f20,f36])).
% 0.39/0.62  fof(f20,plain,(
% 0.39/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f4])).
% 0.39/0.62  fof(f4,axiom,(
% 0.39/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.39/0.62  fof(f30,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f3])).
% 0.39/0.62  fof(f3,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.39/0.62  fof(f40,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f21,f37,f38])).
% 0.39/0.62  fof(f21,plain,(
% 0.39/0.62    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f12])).
% 0.39/0.62  fof(f12,axiom,(
% 0.39/0.62    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.39/0.62  % SZS output end Proof for theBenchmark
% 0.39/0.62  % (21461)------------------------------
% 0.39/0.62  % (21461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.62  % (21461)Termination reason: Refutation
% 0.39/0.62  
% 0.39/0.62  % (21461)Memory used [KB]: 6268
% 0.39/0.62  % (21461)Time elapsed: 0.009 s
% 0.39/0.62  % (21461)------------------------------
% 0.39/0.62  % (21461)------------------------------
% 0.39/0.62  % (21448)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.39/0.62  % (21271)Success in time 0.251 s
%------------------------------------------------------------------------------
