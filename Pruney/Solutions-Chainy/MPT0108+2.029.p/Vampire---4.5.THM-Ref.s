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
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 44.63s
% Output     : Refutation 44.63s
% Verified   : 
% Statistics : Number of formulae       :  139 (9294 expanded)
%              Number of leaves         :   14 (3128 expanded)
%              Depth                    :   37
%              Number of atoms          :  147 (9305 expanded)
%              Number of equality atoms :  135 (9290 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f114,f59968])).

fof(f59968,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f59967])).

fof(f59967,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f113,f59966])).

fof(f59966,plain,(
    ! [X202,X201] : k5_xboole_0(X201,X202) = k4_xboole_0(k5_xboole_0(X201,k4_xboole_0(X202,X201)),k5_xboole_0(X201,k4_xboole_0(X201,X202))) ),
    inference(forward_demodulation,[],[f59564,f59834])).

fof(f59834,plain,(
    ! [X80,X79] : k5_xboole_0(X79,k4_xboole_0(X79,X80)) = k4_xboole_0(X79,k5_xboole_0(X79,X80)) ),
    inference(forward_demodulation,[],[f59833,f5822])).

fof(f5822,plain,(
    ! [X47,X45,X46] : k5_xboole_0(X47,k4_xboole_0(X45,X46)) = k5_xboole_0(X45,k5_xboole_0(X47,k5_xboole_0(X46,k4_xboole_0(X46,X45)))) ),
    inference(forward_demodulation,[],[f5735,f92])).

fof(f92,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f88,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f86,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f79])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f69,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5735,plain,(
    ! [X47,X45,X46] : k5_xboole_0(X47,k4_xboole_0(X45,X46)) = k5_xboole_0(X45,k5_xboole_0(X47,k4_xboole_0(X46,k4_xboole_0(X46,X45)))) ),
    inference(superposition,[],[f133,f1158])).

fof(f1158,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f92,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f133,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f129,f26])).

fof(f129,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f26,f90])).

fof(f90,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f88,f21])).

fof(f59833,plain,(
    ! [X80,X79] : k4_xboole_0(X79,k5_xboole_0(X79,X80)) = k5_xboole_0(X79,k5_xboole_0(X79,k5_xboole_0(X80,k4_xboole_0(X80,X79)))) ),
    inference(forward_demodulation,[],[f59515,f26])).

fof(f59515,plain,(
    ! [X80,X79] : k4_xboole_0(X79,k5_xboole_0(X79,X80)) = k5_xboole_0(X79,k5_xboole_0(k5_xboole_0(X79,X80),k4_xboole_0(X80,X79))) ),
    inference(superposition,[],[f5809,f59154])).

fof(f59154,plain,(
    ! [X99,X100] : k4_xboole_0(X99,X100) = k4_xboole_0(k5_xboole_0(X100,X99),X100) ),
    inference(forward_demodulation,[],[f59153,f37])).

fof(f59153,plain,(
    ! [X99,X100] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X99,X100)) = k4_xboole_0(k5_xboole_0(X100,X99),X100) ),
    inference(forward_demodulation,[],[f59152,f57480])).

fof(f57480,plain,(
    ! [X21,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X21),X20),k4_xboole_0(X21,X20)) ),
    inference(superposition,[],[f14839,f53090])).

fof(f53090,plain,(
    ! [X261,X262] : k4_xboole_0(X262,X261) = k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262)) ),
    inference(forward_demodulation,[],[f53086,f18])).

fof(f53086,plain,(
    ! [X261,X262] : k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262)) = k5_xboole_0(k4_xboole_0(X262,X261),k1_xboole_0) ),
    inference(backward_demodulation,[],[f16504,f52907])).

fof(f52907,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f14956,f13701])).

fof(f13701,plain,(
    ! [X12,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)) ),
    inference(superposition,[],[f143,f5809])).

fof(f143,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k5_xboole_0(X12,X13)),X13) ),
    inference(superposition,[],[f121,f26])).

fof(f121,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f90,f88])).

fof(f14956,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f14955,f37])).

fof(f14955,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f14902,f60])).

fof(f60,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f26,f21])).

fof(f14902,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0))) ),
    inference(superposition,[],[f600,f14839])).

fof(f600,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10))))) ),
    inference(superposition,[],[f29,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f103,f92])).

fof(f103,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(backward_demodulation,[],[f31,f92])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f16504,plain,(
    ! [X261,X262] : k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262)) = k5_xboole_0(k4_xboole_0(X262,X261),k4_xboole_0(k4_xboole_0(X261,X262),k5_xboole_0(X261,X262))) ),
    inference(superposition,[],[f13698,f13702])).

fof(f13702,plain,(
    ! [X14,X13] : k4_xboole_0(X14,X13) = k5_xboole_0(k4_xboole_0(X13,X14),k5_xboole_0(X13,X14)) ),
    inference(superposition,[],[f163,f5809])).

fof(f163,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k5_xboole_0(X12,X13)),k5_xboole_0(X11,X12)) = X13 ),
    inference(superposition,[],[f122,f26])).

fof(f122,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f90,f90])).

fof(f13698,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k5_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f95,f5809])).

fof(f95,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13 ),
    inference(superposition,[],[f88,f26])).

fof(f14839,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f14838,f88])).

fof(f14838,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f14837,f108])).

fof(f14837,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),X11))) ),
    inference(forward_demodulation,[],[f14836,f21])).

fof(f14836,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),X11),X9)) ),
    inference(backward_demodulation,[],[f3717,f14707])).

fof(f14707,plain,(
    ! [X275,X276,X274] : k5_xboole_0(X276,k5_xboole_0(X274,k4_xboole_0(X274,k5_xboole_0(X275,X276)))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X275,X276),X274),X275) ),
    inference(superposition,[],[f314,f5820])).

fof(f5820,plain,(
    ! [X41,X40] : k4_xboole_0(X40,X41) = k5_xboole_0(k5_xboole_0(X41,k4_xboole_0(X41,X40)),X40) ),
    inference(forward_demodulation,[],[f5733,f92])).

fof(f5733,plain,(
    ! [X41,X40] : k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X40)),X40) ),
    inference(superposition,[],[f122,f1158])).

fof(f314,plain,(
    ! [X30,X31,X29] : k5_xboole_0(X30,X31) = k5_xboole_0(k5_xboole_0(X31,k5_xboole_0(X29,X30)),X29) ),
    inference(superposition,[],[f122,f60])).

fof(f3717,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X9,X10)))))) ),
    inference(superposition,[],[f600,f92])).

fof(f59152,plain,(
    ! [X99,X100] : k4_xboole_0(k5_xboole_0(X100,X99),X100) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,X99),X100),k4_xboole_0(X99,X100)),k4_xboole_0(X99,X100)) ),
    inference(forward_demodulation,[],[f58826,f18])).

fof(f58826,plain,(
    ! [X99,X100] : k4_xboole_0(k5_xboole_0(X100,X99),X100) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,X99),X100),k4_xboole_0(X99,X100)),k5_xboole_0(k4_xboole_0(X99,X100),k1_xboole_0)) ),
    inference(superposition,[],[f5816,f54559])).

fof(f54559,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k4_xboole_0(k5_xboole_0(X115,X114),X115)) ),
    inference(forward_demodulation,[],[f54554,f13692])).

fof(f13692,plain,(
    ! [X33,X34] : k5_xboole_0(X34,k4_xboole_0(X33,k5_xboole_0(X33,X34))) = k4_xboole_0(k5_xboole_0(X33,X34),X33) ),
    inference(superposition,[],[f5809,f173])).

fof(f173,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9)) ),
    inference(superposition,[],[f26,f122])).

fof(f54554,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k5_xboole_0(X114,k4_xboole_0(X115,k5_xboole_0(X115,X114)))) ),
    inference(backward_demodulation,[],[f54156,f54553])).

fof(f54553,plain,(
    ! [X35,X34] : k4_xboole_0(X34,k5_xboole_0(X34,X35)) = k4_xboole_0(X35,k4_xboole_0(k5_xboole_0(X34,X35),X34)) ),
    inference(backward_demodulation,[],[f54523,f54551])).

fof(f54551,plain,(
    ! [X83,X84] : k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k4_xboole_0(k5_xboole_0(X83,X84),X83) ),
    inference(forward_demodulation,[],[f54550,f13692])).

fof(f54550,plain,(
    ! [X83,X84] : k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k5_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) ),
    inference(forward_demodulation,[],[f54383,f18])).

fof(f54383,plain,(
    ! [X83,X84] : k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X83,k5_xboole_0(X83,X84)),k1_xboole_0)) ),
    inference(superposition,[],[f5809,f53288])).

fof(f53288,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,k5_xboole_0(X5,X6)),X6) ),
    inference(superposition,[],[f52907,f88])).

fof(f54523,plain,(
    ! [X35,X34] : k4_xboole_0(X34,k5_xboole_0(X34,X35)) = k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k5_xboole_0(X34,X35)))) ),
    inference(forward_demodulation,[],[f54362,f17])).

fof(f54362,plain,(
    ! [X35,X34] : k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k5_xboole_0(X34,X35)))) = k4_xboole_0(k4_xboole_0(X34,k5_xboole_0(X34,X35)),k1_xboole_0) ),
    inference(superposition,[],[f30,f53288])).

fof(f54156,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k5_xboole_0(X115,X114),X115)))) ),
    inference(forward_demodulation,[],[f54155,f18])).

fof(f54155,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k5_xboole_0(X115,X114),X115)))) ),
    inference(forward_demodulation,[],[f54154,f108])).

fof(f54154,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k4_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k5_xboole_0(X115,X114))),X115)) ),
    inference(forward_demodulation,[],[f53931,f5804])).

fof(f5804,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X6)),X8) ),
    inference(forward_demodulation,[],[f5722,f92])).

fof(f5722,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8) ),
    inference(superposition,[],[f108,f1158])).

fof(f53931,plain,(
    ! [X114,X115] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k5_xboole_0(k5_xboole_0(X115,X114),k4_xboole_0(k5_xboole_0(X115,X114),k4_xboole_0(X114,X115)))) ),
    inference(superposition,[],[f5994,f52908])).

fof(f52908,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f14956,f13699])).

fof(f13699,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f125,f5809])).

fof(f125,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13))) ),
    inference(superposition,[],[f90,f26])).

fof(f5994,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f5993,f79])).

fof(f5993,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X11) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f5992,f17])).

fof(f5992,plain,(
    ! [X10,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f5991,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f50,f18])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f29,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f45,f37])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f29,f17])).

fof(f5991,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) = k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X10))) ),
    inference(forward_demodulation,[],[f5949,f108])).

fof(f5949,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),X10) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f5814,f5814])).

fof(f5814,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(backward_demodulation,[],[f1171,f5809])).

fof(f1171,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f1153,f92])).

fof(f1153,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(superposition,[],[f92,f30])).

fof(f5816,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k5_xboole_0(X31,k4_xboole_0(X31,X30))) = X30 ),
    inference(forward_demodulation,[],[f5729,f92])).

fof(f5729,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X31,k4_xboole_0(X31,X30))) = X30 ),
    inference(superposition,[],[f90,f1158])).

fof(f5809,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k5_xboole_0(X29,k4_xboole_0(X29,X28))) ),
    inference(forward_demodulation,[],[f5728,f92])).

fof(f5728,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X29,X28))) ),
    inference(superposition,[],[f88,f1158])).

fof(f59564,plain,(
    ! [X202,X201] : k5_xboole_0(X201,X202) = k4_xboole_0(k5_xboole_0(X201,k4_xboole_0(X202,X201)),k4_xboole_0(X201,k5_xboole_0(X201,X202))) ),
    inference(superposition,[],[f21077,f59154])).

fof(f21077,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) = X8 ),
    inference(forward_demodulation,[],[f21076,f17])).

fof(f21076,plain,(
    ! [X8,X7] : k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f20979,f3794])).

fof(f3794,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f3793,f133])).

fof(f3793,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))))) ),
    inference(forward_demodulation,[],[f3729,f92])).

fof(f3729,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) ),
    inference(superposition,[],[f600,f30])).

fof(f20979,plain,(
    ! [X8,X7] : k4_xboole_0(X8,k4_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f30,f13849])).

fof(f13849,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) ),
    inference(backward_demodulation,[],[f13805,f13848])).

fof(f13848,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f13684,f21])).

fof(f13684,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X6,X5),X5)) ),
    inference(superposition,[],[f5809,f60])).

fof(f13805,plain,(
    ! [X12,X11] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,k5_xboole_0(X12,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f13804,f21])).

fof(f13804,plain,(
    ! [X12,X11] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) ),
    inference(forward_demodulation,[],[f13661,f18])).

fof(f13661,plain,(
    ! [X12,X11] : k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),k5_xboole_0(X11,k1_xboole_0)) ),
    inference(superposition,[],[f5809,f3794])).

fof(f113,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_2
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f114,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f106,f33,f111])).

fof(f33,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f35,f92])).

fof(f35,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f33])).

fof(f28,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f22,f23])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (24299)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (24300)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (24287)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (24289)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (24295)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (24286)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (24297)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (24288)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (24301)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.44/0.53  % (24292)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.44/0.54  % (24290)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.44/0.54  % (24298)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.44/0.54  % (24285)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.44/0.54  % (24296)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.44/0.54  % (24296)Refutation not found, incomplete strategy% (24296)------------------------------
% 1.44/0.54  % (24296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (24296)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (24296)Memory used [KB]: 10490
% 1.44/0.54  % (24296)Time elapsed: 0.107 s
% 1.44/0.54  % (24296)------------------------------
% 1.44/0.54  % (24296)------------------------------
% 1.44/0.54  % (24293)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.44/0.54  % (24284)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.44/0.54  % (24294)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.56/0.56  % (24302)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.41/1.06  % (24288)Time limit reached!
% 5.41/1.06  % (24288)------------------------------
% 5.41/1.06  % (24288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.41/1.06  % (24288)Termination reason: Time limit
% 5.41/1.06  % (24288)Termination phase: Saturation
% 5.41/1.06  
% 5.41/1.06  % (24288)Memory used [KB]: 15607
% 5.41/1.06  % (24288)Time elapsed: 0.600 s
% 5.41/1.06  % (24288)------------------------------
% 5.41/1.06  % (24288)------------------------------
% 11.99/1.93  % (24290)Time limit reached!
% 11.99/1.93  % (24290)------------------------------
% 11.99/1.93  % (24290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.99/1.93  % (24290)Termination reason: Time limit
% 11.99/1.93  % (24290)Termination phase: Saturation
% 11.99/1.93  
% 11.99/1.93  % (24290)Memory used [KB]: 40041
% 11.99/1.93  % (24290)Time elapsed: 1.500 s
% 11.99/1.93  % (24290)------------------------------
% 11.99/1.93  % (24290)------------------------------
% 12.56/1.97  % (24289)Time limit reached!
% 12.56/1.97  % (24289)------------------------------
% 12.56/1.97  % (24289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.87/1.98  % (24289)Termination reason: Time limit
% 12.87/1.98  % (24289)Termination phase: Saturation
% 12.87/1.98  
% 12.87/1.98  % (24289)Memory used [KB]: 40425
% 12.87/1.98  % (24289)Time elapsed: 1.500 s
% 12.87/1.98  % (24289)------------------------------
% 12.87/1.98  % (24289)------------------------------
% 15.04/2.24  % (24286)Time limit reached!
% 15.04/2.24  % (24286)------------------------------
% 15.04/2.24  % (24286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.04/2.24  % (24286)Termination reason: Time limit
% 15.04/2.24  
% 15.04/2.24  % (24286)Memory used [KB]: 43368
% 15.04/2.24  % (24286)Time elapsed: 1.802 s
% 15.04/2.24  % (24286)------------------------------
% 15.04/2.24  % (24286)------------------------------
% 18.31/2.66  % (24297)Time limit reached!
% 18.31/2.66  % (24297)------------------------------
% 18.31/2.66  % (24297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.31/2.66  % (24297)Termination reason: Time limit
% 18.31/2.66  % (24297)Termination phase: Saturation
% 18.31/2.66  
% 18.31/2.66  % (24297)Memory used [KB]: 46694
% 18.31/2.66  % (24297)Time elapsed: 2.200 s
% 18.31/2.66  % (24297)------------------------------
% 18.31/2.66  % (24297)------------------------------
% 44.63/5.98  % (24295)Refutation found. Thanks to Tanya!
% 44.63/5.98  % SZS status Theorem for theBenchmark
% 44.63/5.98  % SZS output start Proof for theBenchmark
% 44.63/5.98  fof(f60011,plain,(
% 44.63/5.98    $false),
% 44.63/5.98    inference(avatar_sat_refutation,[],[f36,f114,f59968])).
% 44.63/5.98  fof(f59968,plain,(
% 44.63/5.98    spl2_2),
% 44.63/5.98    inference(avatar_contradiction_clause,[],[f59967])).
% 44.63/5.98  fof(f59967,plain,(
% 44.63/5.98    $false | spl2_2),
% 44.63/5.98    inference(subsumption_resolution,[],[f113,f59966])).
% 44.63/5.98  fof(f59966,plain,(
% 44.63/5.98    ( ! [X202,X201] : (k5_xboole_0(X201,X202) = k4_xboole_0(k5_xboole_0(X201,k4_xboole_0(X202,X201)),k5_xboole_0(X201,k4_xboole_0(X201,X202)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f59564,f59834])).
% 44.63/5.98  fof(f59834,plain,(
% 44.63/5.98    ( ! [X80,X79] : (k5_xboole_0(X79,k4_xboole_0(X79,X80)) = k4_xboole_0(X79,k5_xboole_0(X79,X80))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f59833,f5822])).
% 44.63/5.98  fof(f5822,plain,(
% 44.63/5.98    ( ! [X47,X45,X46] : (k5_xboole_0(X47,k4_xboole_0(X45,X46)) = k5_xboole_0(X45,k5_xboole_0(X47,k5_xboole_0(X46,k4_xboole_0(X46,X45))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5735,f92])).
% 44.63/5.98  fof(f92,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 44.63/5.98    inference(superposition,[],[f88,f27])).
% 44.63/5.98  fof(f27,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 44.63/5.98    inference(definition_unfolding,[],[f24,f23])).
% 44.63/5.98  fof(f23,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 44.63/5.98    inference(cnf_transformation,[],[f6])).
% 44.63/5.98  fof(f6,axiom,(
% 44.63/5.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 44.63/5.98  fof(f24,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 44.63/5.98    inference(cnf_transformation,[],[f3])).
% 44.63/5.98  fof(f3,axiom,(
% 44.63/5.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 44.63/5.98  fof(f88,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 44.63/5.98    inference(forward_demodulation,[],[f86,f37])).
% 44.63/5.98  fof(f37,plain,(
% 44.63/5.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 44.63/5.98    inference(superposition,[],[f21,f18])).
% 44.63/5.98  fof(f18,plain,(
% 44.63/5.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 44.63/5.98    inference(cnf_transformation,[],[f8])).
% 44.63/5.98  fof(f8,axiom,(
% 44.63/5.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 44.63/5.98  fof(f21,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 44.63/5.98    inference(cnf_transformation,[],[f2])).
% 44.63/5.98  fof(f2,axiom,(
% 44.63/5.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 44.63/5.98  fof(f86,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 44.63/5.98    inference(superposition,[],[f26,f79])).
% 44.63/5.98  fof(f79,plain,(
% 44.63/5.98    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f69,f17])).
% 44.63/5.98  fof(f17,plain,(
% 44.63/5.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 44.63/5.98    inference(cnf_transformation,[],[f4])).
% 44.63/5.98  fof(f4,axiom,(
% 44.63/5.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 44.63/5.98  fof(f69,plain,(
% 44.63/5.98    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 44.63/5.98    inference(superposition,[],[f27,f29])).
% 44.63/5.98  fof(f29,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 44.63/5.98    inference(definition_unfolding,[],[f19,f22])).
% 44.63/5.98  fof(f22,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 44.63/5.98    inference(cnf_transformation,[],[f10])).
% 44.63/5.98  fof(f10,axiom,(
% 44.63/5.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 44.63/5.98  fof(f19,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 44.63/5.98    inference(cnf_transformation,[],[f5])).
% 44.63/5.98  fof(f5,axiom,(
% 44.63/5.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 44.63/5.98  fof(f26,plain,(
% 44.63/5.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 44.63/5.98    inference(cnf_transformation,[],[f9])).
% 44.63/5.98  fof(f9,axiom,(
% 44.63/5.98    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 44.63/5.98  fof(f5735,plain,(
% 44.63/5.98    ( ! [X47,X45,X46] : (k5_xboole_0(X47,k4_xboole_0(X45,X46)) = k5_xboole_0(X45,k5_xboole_0(X47,k4_xboole_0(X46,k4_xboole_0(X46,X45))))) )),
% 44.63/5.98    inference(superposition,[],[f133,f1158])).
% 44.63/5.98  fof(f1158,plain,(
% 44.63/5.98    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 44.63/5.98    inference(superposition,[],[f92,f30])).
% 44.63/5.98  fof(f30,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 44.63/5.98    inference(definition_unfolding,[],[f20,f23,f23])).
% 44.63/5.98  fof(f20,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 44.63/5.98    inference(cnf_transformation,[],[f1])).
% 44.63/5.98  fof(f1,axiom,(
% 44.63/5.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 44.63/5.98  fof(f133,plain,(
% 44.63/5.98    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f129,f26])).
% 44.63/5.98  fof(f129,plain,(
% 44.63/5.98    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 44.63/5.98    inference(superposition,[],[f26,f90])).
% 44.63/5.98  fof(f90,plain,(
% 44.63/5.98    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 44.63/5.98    inference(superposition,[],[f88,f21])).
% 44.63/5.98  fof(f59833,plain,(
% 44.63/5.98    ( ! [X80,X79] : (k4_xboole_0(X79,k5_xboole_0(X79,X80)) = k5_xboole_0(X79,k5_xboole_0(X79,k5_xboole_0(X80,k4_xboole_0(X80,X79))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f59515,f26])).
% 44.63/5.98  fof(f59515,plain,(
% 44.63/5.98    ( ! [X80,X79] : (k4_xboole_0(X79,k5_xboole_0(X79,X80)) = k5_xboole_0(X79,k5_xboole_0(k5_xboole_0(X79,X80),k4_xboole_0(X80,X79)))) )),
% 44.63/5.98    inference(superposition,[],[f5809,f59154])).
% 44.63/5.98  fof(f59154,plain,(
% 44.63/5.98    ( ! [X99,X100] : (k4_xboole_0(X99,X100) = k4_xboole_0(k5_xboole_0(X100,X99),X100)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f59153,f37])).
% 44.63/5.98  fof(f59153,plain,(
% 44.63/5.98    ( ! [X99,X100] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X99,X100)) = k4_xboole_0(k5_xboole_0(X100,X99),X100)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f59152,f57480])).
% 44.63/5.98  fof(f57480,plain,(
% 44.63/5.98    ( ! [X21,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X21),X20),k4_xboole_0(X21,X20))) )),
% 44.63/5.98    inference(superposition,[],[f14839,f53090])).
% 44.63/5.98  fof(f53090,plain,(
% 44.63/5.98    ( ! [X261,X262] : (k4_xboole_0(X262,X261) = k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f53086,f18])).
% 44.63/5.98  fof(f53086,plain,(
% 44.63/5.98    ( ! [X261,X262] : (k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262)) = k5_xboole_0(k4_xboole_0(X262,X261),k1_xboole_0)) )),
% 44.63/5.98    inference(backward_demodulation,[],[f16504,f52907])).
% 44.63/5.98  fof(f52907,plain,(
% 44.63/5.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 44.63/5.98    inference(superposition,[],[f14956,f13701])).
% 44.63/5.98  fof(f13701,plain,(
% 44.63/5.98    ( ! [X12,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11))) )),
% 44.63/5.98    inference(superposition,[],[f143,f5809])).
% 44.63/5.98  fof(f143,plain,(
% 44.63/5.98    ( ! [X12,X13,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,k5_xboole_0(X12,X13)),X13)) )),
% 44.63/5.98    inference(superposition,[],[f121,f26])).
% 44.63/5.98  fof(f121,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 44.63/5.98    inference(superposition,[],[f90,f88])).
% 44.63/5.98  fof(f14956,plain,(
% 44.63/5.98    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f14955,f37])).
% 44.63/5.98  fof(f14955,plain,(
% 44.63/5.98    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X4,X5))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f14902,f60])).
% 44.63/5.98  fof(f60,plain,(
% 44.63/5.98    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 44.63/5.98    inference(superposition,[],[f26,f21])).
% 44.63/5.98  fof(f14902,plain,(
% 44.63/5.98    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)))) )),
% 44.63/5.98    inference(superposition,[],[f600,f14839])).
% 44.63/5.98  fof(f600,plain,(
% 44.63/5.98    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X10,k5_xboole_0(X10,k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))) )),
% 44.63/5.98    inference(superposition,[],[f29,f108])).
% 44.63/5.98  fof(f108,plain,(
% 44.63/5.98    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f103,f92])).
% 44.63/5.98  fof(f103,plain,(
% 44.63/5.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 44.63/5.98    inference(backward_demodulation,[],[f31,f92])).
% 44.63/5.98  fof(f31,plain,(
% 44.63/5.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 44.63/5.98    inference(definition_unfolding,[],[f25,f23,f23])).
% 44.63/5.98  fof(f25,plain,(
% 44.63/5.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 44.63/5.98    inference(cnf_transformation,[],[f7])).
% 44.63/5.98  fof(f7,axiom,(
% 44.63/5.98    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 44.63/5.98  fof(f16504,plain,(
% 44.63/5.98    ( ! [X261,X262] : (k4_xboole_0(k5_xboole_0(X261,X262),k4_xboole_0(X261,X262)) = k5_xboole_0(k4_xboole_0(X262,X261),k4_xboole_0(k4_xboole_0(X261,X262),k5_xboole_0(X261,X262)))) )),
% 44.63/5.98    inference(superposition,[],[f13698,f13702])).
% 44.63/5.98  fof(f13702,plain,(
% 44.63/5.98    ( ! [X14,X13] : (k4_xboole_0(X14,X13) = k5_xboole_0(k4_xboole_0(X13,X14),k5_xboole_0(X13,X14))) )),
% 44.63/5.98    inference(superposition,[],[f163,f5809])).
% 44.63/5.98  fof(f163,plain,(
% 44.63/5.98    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k5_xboole_0(X12,X13)),k5_xboole_0(X11,X12)) = X13) )),
% 44.63/5.98    inference(superposition,[],[f122,f26])).
% 44.63/5.98  fof(f122,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 44.63/5.98    inference(superposition,[],[f90,f90])).
% 44.63/5.98  fof(f13698,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k5_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 44.63/5.98    inference(superposition,[],[f95,f5809])).
% 44.63/5.98  fof(f95,plain,(
% 44.63/5.98    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13) )),
% 44.63/5.98    inference(superposition,[],[f88,f26])).
% 44.63/5.98  fof(f14839,plain,(
% 44.63/5.98    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X11)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f14838,f88])).
% 44.63/5.98  fof(f14838,plain,(
% 44.63/5.98    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k5_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X11)))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f14837,f108])).
% 44.63/5.98  fof(f14837,plain,(
% 44.63/5.98    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),X11)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f14836,f21])).
% 44.63/5.98  fof(f14836,plain,(
% 44.63/5.98    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),X11),X9))) )),
% 44.63/5.98    inference(backward_demodulation,[],[f3717,f14707])).
% 44.63/5.98  fof(f14707,plain,(
% 44.63/5.98    ( ! [X275,X276,X274] : (k5_xboole_0(X276,k5_xboole_0(X274,k4_xboole_0(X274,k5_xboole_0(X275,X276)))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X275,X276),X274),X275)) )),
% 44.63/5.98    inference(superposition,[],[f314,f5820])).
% 44.63/5.98  fof(f5820,plain,(
% 44.63/5.98    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k5_xboole_0(k5_xboole_0(X41,k4_xboole_0(X41,X40)),X40)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5733,f92])).
% 44.63/5.98  fof(f5733,plain,(
% 44.63/5.98    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X40)),X40)) )),
% 44.63/5.98    inference(superposition,[],[f122,f1158])).
% 44.63/5.98  fof(f314,plain,(
% 44.63/5.98    ( ! [X30,X31,X29] : (k5_xboole_0(X30,X31) = k5_xboole_0(k5_xboole_0(X31,k5_xboole_0(X29,X30)),X29)) )),
% 44.63/5.98    inference(superposition,[],[f122,f60])).
% 44.63/5.98  fof(f3717,plain,(
% 44.63/5.98    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(k4_xboole_0(X9,X10),k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X9,X10))))))) )),
% 44.63/5.98    inference(superposition,[],[f600,f92])).
% 44.63/5.98  fof(f59152,plain,(
% 44.63/5.98    ( ! [X99,X100] : (k4_xboole_0(k5_xboole_0(X100,X99),X100) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,X99),X100),k4_xboole_0(X99,X100)),k4_xboole_0(X99,X100))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f58826,f18])).
% 44.63/5.98  fof(f58826,plain,(
% 44.63/5.98    ( ! [X99,X100] : (k4_xboole_0(k5_xboole_0(X100,X99),X100) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,X99),X100),k4_xboole_0(X99,X100)),k5_xboole_0(k4_xboole_0(X99,X100),k1_xboole_0))) )),
% 44.63/5.98    inference(superposition,[],[f5816,f54559])).
% 44.63/5.98  fof(f54559,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k4_xboole_0(k5_xboole_0(X115,X114),X115))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54554,f13692])).
% 44.63/5.98  fof(f13692,plain,(
% 44.63/5.98    ( ! [X33,X34] : (k5_xboole_0(X34,k4_xboole_0(X33,k5_xboole_0(X33,X34))) = k4_xboole_0(k5_xboole_0(X33,X34),X33)) )),
% 44.63/5.98    inference(superposition,[],[f5809,f173])).
% 44.63/5.98  fof(f173,plain,(
% 44.63/5.98    ( ! [X8,X7,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9))) )),
% 44.63/5.98    inference(superposition,[],[f26,f122])).
% 44.63/5.98  fof(f54554,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k5_xboole_0(X114,k4_xboole_0(X115,k5_xboole_0(X115,X114))))) )),
% 44.63/5.98    inference(backward_demodulation,[],[f54156,f54553])).
% 44.63/5.98  fof(f54553,plain,(
% 44.63/5.98    ( ! [X35,X34] : (k4_xboole_0(X34,k5_xboole_0(X34,X35)) = k4_xboole_0(X35,k4_xboole_0(k5_xboole_0(X34,X35),X34))) )),
% 44.63/5.98    inference(backward_demodulation,[],[f54523,f54551])).
% 44.63/5.98  fof(f54551,plain,(
% 44.63/5.98    ( ! [X83,X84] : (k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k4_xboole_0(k5_xboole_0(X83,X84),X83)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54550,f13692])).
% 44.63/5.98  fof(f54550,plain,(
% 44.63/5.98    ( ! [X83,X84] : (k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k5_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54383,f18])).
% 44.63/5.98  fof(f54383,plain,(
% 44.63/5.98    ( ! [X83,X84] : (k4_xboole_0(X84,k4_xboole_0(X83,k5_xboole_0(X83,X84))) = k5_xboole_0(X84,k5_xboole_0(k4_xboole_0(X83,k5_xboole_0(X83,X84)),k1_xboole_0))) )),
% 44.63/5.98    inference(superposition,[],[f5809,f53288])).
% 44.63/5.98  fof(f53288,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,k5_xboole_0(X5,X6)),X6)) )),
% 44.63/5.98    inference(superposition,[],[f52907,f88])).
% 44.63/5.98  fof(f54523,plain,(
% 44.63/5.98    ( ! [X35,X34] : (k4_xboole_0(X34,k5_xboole_0(X34,X35)) = k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k5_xboole_0(X34,X35))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54362,f17])).
% 44.63/5.98  fof(f54362,plain,(
% 44.63/5.98    ( ! [X35,X34] : (k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X34,k5_xboole_0(X34,X35)))) = k4_xboole_0(k4_xboole_0(X34,k5_xboole_0(X34,X35)),k1_xboole_0)) )),
% 44.63/5.98    inference(superposition,[],[f30,f53288])).
% 44.63/5.98  fof(f54156,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X114,X115),k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k5_xboole_0(X115,X114),X115))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54155,f18])).
% 44.63/5.98  fof(f54155,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k5_xboole_0(X115,X114),X115))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f54154,f108])).
% 44.63/5.98  fof(f54154,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k4_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k5_xboole_0(X115,X114))),X115))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f53931,f5804])).
% 44.63/5.98  fof(f5804,plain,(
% 44.63/5.98    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5722,f92])).
% 44.63/5.98  fof(f5722,plain,(
% 44.63/5.98    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) )),
% 44.63/5.98    inference(superposition,[],[f108,f1158])).
% 44.63/5.98  fof(f53931,plain,(
% 44.63/5.98    ( ! [X114,X115] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X114,X115),k1_xboole_0),k5_xboole_0(k5_xboole_0(X115,X114),k4_xboole_0(k5_xboole_0(X115,X114),k4_xboole_0(X114,X115))))) )),
% 44.63/5.98    inference(superposition,[],[f5994,f52908])).
% 44.63/5.98  fof(f52908,plain,(
% 44.63/5.98    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 44.63/5.98    inference(superposition,[],[f14956,f13699])).
% 44.63/5.98  fof(f13699,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))) )),
% 44.63/5.98    inference(superposition,[],[f125,f5809])).
% 44.63/5.98  fof(f125,plain,(
% 44.63/5.98    ( ! [X12,X13,X11] : (k5_xboole_0(X11,X12) = k5_xboole_0(X13,k5_xboole_0(X11,k5_xboole_0(X12,X13)))) )),
% 44.63/5.98    inference(superposition,[],[f90,f26])).
% 44.63/5.98  fof(f5994,plain,(
% 44.63/5.98    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5993,f79])).
% 44.63/5.98  fof(f5993,plain,(
% 44.63/5.98    ( ! [X10,X11] : (k5_xboole_0(X11,X11) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5992,f17])).
% 44.63/5.98  fof(f5992,plain,(
% 44.63/5.98    ( ! [X10,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5991,f51])).
% 44.63/5.98  fof(f51,plain,(
% 44.63/5.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f50,f18])).
% 44.63/5.98  fof(f50,plain,(
% 44.63/5.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 44.63/5.98    inference(superposition,[],[f29,f48])).
% 44.63/5.98  fof(f48,plain,(
% 44.63/5.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f45,f37])).
% 44.63/5.98  fof(f45,plain,(
% 44.63/5.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 44.63/5.98    inference(superposition,[],[f29,f17])).
% 44.63/5.98  fof(f5991,plain,(
% 44.63/5.98    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11))) = k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X10)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5949,f108])).
% 44.63/5.98  fof(f5949,plain,(
% 44.63/5.98    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),X10) = k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X10)),k5_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 44.63/5.98    inference(superposition,[],[f5814,f5814])).
% 44.63/5.98  fof(f5814,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 44.63/5.98    inference(backward_demodulation,[],[f1171,f5809])).
% 44.63/5.98  fof(f1171,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5))) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f1153,f92])).
% 44.63/5.98  fof(f1153,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 44.63/5.98    inference(superposition,[],[f92,f30])).
% 44.63/5.98  fof(f5816,plain,(
% 44.63/5.98    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k5_xboole_0(X31,k4_xboole_0(X31,X30))) = X30) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5729,f92])).
% 44.63/5.98  fof(f5729,plain,(
% 44.63/5.98    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X31,k4_xboole_0(X31,X30))) = X30) )),
% 44.63/5.98    inference(superposition,[],[f90,f1158])).
% 44.63/5.98  fof(f5809,plain,(
% 44.63/5.98    ( ! [X28,X29] : (k4_xboole_0(X28,X29) = k5_xboole_0(X28,k5_xboole_0(X29,k4_xboole_0(X29,X28)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f5728,f92])).
% 44.63/5.98  fof(f5728,plain,(
% 44.63/5.98    ( ! [X28,X29] : (k4_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,k4_xboole_0(X29,X28)))) )),
% 44.63/5.98    inference(superposition,[],[f88,f1158])).
% 44.63/5.98  fof(f59564,plain,(
% 44.63/5.98    ( ! [X202,X201] : (k5_xboole_0(X201,X202) = k4_xboole_0(k5_xboole_0(X201,k4_xboole_0(X202,X201)),k4_xboole_0(X201,k5_xboole_0(X201,X202)))) )),
% 44.63/5.98    inference(superposition,[],[f21077,f59154])).
% 44.63/5.98  fof(f21077,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8)) = X8) )),
% 44.63/5.98    inference(forward_demodulation,[],[f21076,f17])).
% 44.63/5.98  fof(f21076,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f20979,f3794])).
% 44.63/5.98  fof(f3794,plain,(
% 44.63/5.98    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f3793,f133])).
% 44.63/5.98  fof(f3793,plain,(
% 44.63/5.98    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2)))))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f3729,f92])).
% 44.63/5.98  fof(f3729,plain,(
% 44.63/5.98    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))) )),
% 44.63/5.98    inference(superposition,[],[f600,f30])).
% 44.63/5.98  fof(f20979,plain,(
% 44.63/5.98    ( ! [X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),k4_xboole_0(X7,X8))) )),
% 44.63/5.98    inference(superposition,[],[f30,f13849])).
% 44.63/5.98  fof(f13849,plain,(
% 44.63/5.98    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11)) )),
% 44.63/5.98    inference(backward_demodulation,[],[f13805,f13848])).
% 44.63/5.98  fof(f13848,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f13684,f21])).
% 44.63/5.98  fof(f13684,plain,(
% 44.63/5.98    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X6,X5),X5))) )),
% 44.63/5.98    inference(superposition,[],[f5809,f60])).
% 44.63/5.98  fof(f13805,plain,(
% 44.63/5.98    ( ! [X12,X11] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,k5_xboole_0(X12,k4_xboole_0(X11,X12)))) )),
% 44.63/5.98    inference(forward_demodulation,[],[f13804,f21])).
% 44.63/5.98  fof(f13804,plain,(
% 44.63/5.98    ( ! [X12,X11] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11)) )),
% 44.63/5.98    inference(forward_demodulation,[],[f13661,f18])).
% 44.63/5.98  fof(f13661,plain,(
% 44.63/5.98    ( ! [X12,X11] : (k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(X11,X12)),k5_xboole_0(X11,k1_xboole_0))) )),
% 44.63/5.98    inference(superposition,[],[f5809,f3794])).
% 44.63/5.98  fof(f113,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_2),
% 44.63/5.98    inference(avatar_component_clause,[],[f111])).
% 44.63/5.98  fof(f111,plain,(
% 44.63/5.98    spl2_2 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 44.63/5.98    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 44.63/5.98  fof(f114,plain,(
% 44.63/5.98    ~spl2_2 | spl2_1),
% 44.63/5.98    inference(avatar_split_clause,[],[f106,f33,f111])).
% 44.63/5.98  fof(f33,plain,(
% 44.63/5.98    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 44.63/5.98    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 44.63/5.98  fof(f106,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 44.63/5.98    inference(backward_demodulation,[],[f35,f92])).
% 44.63/5.98  fof(f35,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 44.63/5.98    inference(avatar_component_clause,[],[f33])).
% 44.63/5.98  fof(f36,plain,(
% 44.63/5.98    ~spl2_1),
% 44.63/5.98    inference(avatar_split_clause,[],[f28,f33])).
% 44.63/5.98  fof(f28,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 44.63/5.98    inference(definition_unfolding,[],[f16,f22,f23])).
% 44.63/5.98  fof(f16,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 44.63/5.98    inference(cnf_transformation,[],[f15])).
% 44.63/5.98  fof(f15,plain,(
% 44.63/5.98    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 44.63/5.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 44.63/5.98  fof(f14,plain,(
% 44.63/5.98    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 44.63/5.98    introduced(choice_axiom,[])).
% 44.63/5.98  fof(f13,plain,(
% 44.63/5.98    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 44.63/5.98    inference(ennf_transformation,[],[f12])).
% 44.63/5.98  fof(f12,negated_conjecture,(
% 44.63/5.98    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 44.63/5.98    inference(negated_conjecture,[],[f11])).
% 44.63/5.98  fof(f11,conjecture,(
% 44.63/5.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 44.63/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 44.63/5.98  % SZS output end Proof for theBenchmark
% 44.63/5.98  % (24295)------------------------------
% 44.63/5.98  % (24295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 44.63/5.98  % (24295)Termination reason: Refutation
% 44.63/5.98  
% 44.63/5.98  % (24295)Memory used [KB]: 153131
% 44.63/5.98  % (24295)Time elapsed: 5.545 s
% 44.63/5.98  % (24295)------------------------------
% 44.63/5.98  % (24295)------------------------------
% 44.63/5.99  % (24283)Success in time 5.633 s
%------------------------------------------------------------------------------
