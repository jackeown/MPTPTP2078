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
% DateTime   : Thu Dec  3 13:09:18 EST 2020

% Result     : CounterSatisfiable 1.54s
% Output     : Saturation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 113 expanded)
%              Number of leaves         :  113 ( 113 expanded)
%              Depth                    :    0
%              Number of atoms          :  162 ( 162 expanded)
%              Number of equality atoms :   92 (  92 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u3444,negated_conjecture,
    ( ~ ( sK1 != k2_pre_topc(sK0,sK1) )
    | sK1 != k2_pre_topc(sK0,sK1) )).

tff(u3443,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u3442,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) )).

tff(u3441,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X5)) )).

tff(u3440,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) )).

tff(u3439,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) )).

tff(u3438,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) )).

tff(u3437,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u3436,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

tff(u3435,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X5)) )).

tff(u3434,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u3433,axiom,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) )).

tff(u3432,axiom,(
    ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X8,X7) )).

tff(u3431,axiom,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u3430,axiom,(
    ! [X5,X7,X6] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k7_subset_1(X5,k4_xboole_0(X5,X6),X7) )).

tff(u3429,axiom,(
    ! [X1,X0] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) )).

tff(u3428,axiom,(
    ! [X5,X6] : k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) )).

tff(u3427,axiom,(
    ! [X69,X71,X70] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X69,X70),X70),X71) = k7_subset_1(k4_xboole_0(k3_xboole_0(X69,X70),X69),k4_xboole_0(k3_xboole_0(X69,X70),X70),X71) )).

tff(u3426,axiom,(
    ! [X27,X28] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X27,X28),X28),k4_xboole_0(k3_xboole_0(X27,X28),X27)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X27,X28),X28),k3_xboole_0(X27,X28)) )).

tff(u3425,axiom,(
    ! [X46,X47] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X46,X47),X47),k4_xboole_0(k3_xboole_0(X46,X47),X46)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X46,X47),X47),k3_xboole_0(X46,X47)) )).

tff(u3424,axiom,(
    ! [X75,X77,X76] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X75,X76),X75),X77) = k7_subset_1(k4_xboole_0(k3_xboole_0(X75,X76),X76),k4_xboole_0(k3_xboole_0(X75,X76),X75),X77) )).

tff(u3423,axiom,(
    ! [X16,X17] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X16,X17),X16),k4_xboole_0(k3_xboole_0(X16,X17),X17)) )).

tff(u3422,axiom,(
    ! [X25,X24] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),X24),k3_xboole_0(X24,X25)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),X24),k4_xboole_0(k3_xboole_0(X24,X25),X25)) )).

tff(u3421,axiom,(
    ! [X11,X10] : k4_xboole_0(k3_xboole_0(X10,X11),X10) = k4_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X10,X11)) )).

tff(u3420,axiom,(
    ! [X16,X17] : k4_xboole_0(k3_xboole_0(X17,X16),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X17,X16),X17) )).

tff(u3419,axiom,(
    ! [X3,X2] : k4_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k3_xboole_0(X2,X3),X2) )).

tff(u3418,axiom,(
    ! [X20,X19] : k4_xboole_0(k3_xboole_0(X20,X19),X19) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X20,X19)) )).

tff(u3417,axiom,(
    ! [X23,X24] : k4_xboole_0(k3_xboole_0(X24,X23),X23) = k4_xboole_0(k3_xboole_0(X24,X23),k3_xboole_0(X23,X24)) )).

tff(u3416,axiom,(
    ! [X25,X24] : k4_xboole_0(k3_xboole_0(X24,X25),X25) = k3_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(k3_xboole_0(X24,X25),X24)) )).

tff(u3415,axiom,(
    ! [X1,X2] : k4_xboole_0(k3_xboole_0(X2,X1),X2) = k3_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(k3_xboole_0(X2,X1),X1)) )).

tff(u3414,axiom,(
    ! [X15,X14] : k4_xboole_0(k3_xboole_0(X14,X15),X15) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X14,X15),X15),k4_xboole_0(k3_xboole_0(X14,X15),X14)) )).

tff(u3413,axiom,(
    ! [X32,X33] : k4_xboole_0(k3_xboole_0(X32,X33),X33) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X32,X33),X32),k4_xboole_0(k3_xboole_0(X32,X33),X33)) )).

tff(u3412,axiom,(
    ! [X55,X54] : k4_xboole_0(k3_xboole_0(X54,X55),X54) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X54,X55),X55),k4_xboole_0(k3_xboole_0(X54,X55),X54)) )).

tff(u3411,axiom,(
    ! [X58,X59] : k4_xboole_0(k3_xboole_0(X58,X59),X58) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X58,X59),X58),k4_xboole_0(k3_xboole_0(X58,X59),X59)) )).

tff(u3410,axiom,(
    ! [X38,X39] : k4_xboole_0(k3_xboole_0(X38,X39),X39) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X38,X39),X38),k3_xboole_0(X38,X39)) )).

tff(u3409,axiom,(
    ! [X93,X94] : k4_xboole_0(k3_xboole_0(X93,X94),X93) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X93,X94),X94),k3_xboole_0(X93,X94)) )).

tff(u3408,axiom,(
    ! [X1,X0] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

tff(u3407,axiom,(
    ! [X20,X19] : k4_xboole_0(k3_xboole_0(X20,X19),X20) = k5_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) )).

tff(u3406,axiom,(
    ! [X18,X17] : k4_xboole_0(k3_xboole_0(X18,X17),X17) = k5_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X17,X18)) )).

tff(u3405,axiom,(
    ! [X11,X13,X12] : k4_xboole_0(k3_xboole_0(X11,X12),X13) = k7_subset_1(X11,k3_xboole_0(X11,X12),X13) )).

tff(u3404,axiom,(
    ! [X16,X15,X14] : k4_xboole_0(k3_xboole_0(X14,X15),X16) = k7_subset_1(X15,k3_xboole_0(X14,X15),X16) )).

tff(u3403,axiom,(
    ! [X20,X22,X21] : k4_xboole_0(k3_xboole_0(X20,X21),X22) = k7_subset_1(k3_xboole_0(X21,X20),k3_xboole_0(X20,X21),X22) )).

tff(u3402,negated_conjecture,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u3401,negated_conjecture,(
    k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) )).

tff(u3400,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

tff(u3399,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2)) )).

tff(u3398,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3)) )).

tff(u3397,axiom,(
    ! [X20,X21] : k3_xboole_0(X21,X20) = k4_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(k3_xboole_0(X20,X21),X21)) )).

tff(u3396,axiom,(
    ! [X25,X24] : k3_xboole_0(X25,X24) = k4_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(k3_xboole_0(X24,X25),X24)) )).

tff(u3395,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

tff(u3394,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u3393,axiom,(
    ! [X7,X6] : k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X7,X6),X6) )).

tff(u3392,axiom,(
    ! [X5,X4] : k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X4,X5)) )).

tff(u3391,axiom,(
    ! [X1,X0] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) )).

tff(u3390,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

tff(u3389,axiom,(
    ! [X27,X28] : k3_xboole_0(X27,X28) = k3_xboole_0(k3_xboole_0(X28,X27),k3_xboole_0(X27,X28)) )).

tff(u3388,axiom,(
    ! [X5,X4] : k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X5,X4)) )).

tff(u3387,axiom,(
    ! [X9,X10] : k3_xboole_0(X10,X9) = k3_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,X10)) )).

tff(u3386,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) )).

tff(u3385,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) )).

tff(u3384,axiom,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),X16)) )).

tff(u3383,axiom,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),X17)) )).

tff(u3382,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u3381,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

tff(u3380,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u3379,axiom,(
    ! [X7,X6] : k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,X6) )).

tff(u3378,axiom,(
    ! [X9,X8] : k3_xboole_0(k3_xboole_0(X8,X9),X8) = k3_xboole_0(X9,X8) )).

tff(u3377,axiom,(
    ! [X13,X14] : k4_xboole_0(k3_xboole_0(X14,X13),X13) = k5_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X14,X13)) )).

tff(u3376,axiom,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u3375,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u3374,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u3373,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u3372,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u3371,negated_conjecture,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u3370,negated_conjecture,(
    sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u3369,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k4_xboole_0(X4,X5) = k7_subset_1(X3,X4,X5) ) )).

tff(u3368,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u3367,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X1,u1_struct_0(X2))
      | k2_pre_topc(X2,X1) = X1
      | ~ l1_pre_topc(X2)
      | ~ v4_pre_topc(X1,X2) ) )).

tff(u3366,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u3365,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u3364,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u3363,axiom,(
    ! [X5,X4] : r1_tarski(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) )).

tff(u3362,axiom,(
    ! [X13,X12] : r1_tarski(k4_xboole_0(k3_xboole_0(X12,X13),X13),k4_xboole_0(k3_xboole_0(X12,X13),X12)) )).

tff(u3361,axiom,(
    ! [X44,X45] : r1_tarski(k4_xboole_0(k3_xboole_0(X44,X45),X44),k4_xboole_0(k3_xboole_0(X44,X45),X45)) )).

tff(u3360,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u3359,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) )).

tff(u3358,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

tff(u3357,axiom,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),k3_xboole_0(X14,X13)) )).

tff(u3356,negated_conjecture,(
    r1_tarski(sK1,sK1) )).

tff(u3355,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u3354,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u3353,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_xboole_0(X2,X3) = X2 ) )).

tff(u3352,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) )).

tff(u3351,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u3350,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u3349,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u3348,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u3347,axiom,(
    ! [X3,X4] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X3),X4),X3)
      | ~ l1_pre_topc(X3)
      | k4_xboole_0(u1_struct_0(X3),X4) = k2_pre_topc(X3,k4_xboole_0(u1_struct_0(X3),X4)) ) )).

tff(u3346,axiom,(
    ! [X5,X6] :
      ( ~ v4_pre_topc(k3_xboole_0(u1_struct_0(X5),X6),X5)
      | ~ l1_pre_topc(X5)
      | k3_xboole_0(u1_struct_0(X5),X6) = k2_pre_topc(X5,k3_xboole_0(u1_struct_0(X5),X6)) ) )).

tff(u3345,axiom,(
    ! [X7,X8] :
      ( ~ v4_pre_topc(k3_xboole_0(X8,u1_struct_0(X7)),X7)
      | ~ l1_pre_topc(X7)
      | k3_xboole_0(X8,u1_struct_0(X7)) = k2_pre_topc(X7,k3_xboole_0(X8,u1_struct_0(X7))) ) )).

tff(u3344,axiom,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) )).

tff(u3343,negated_conjecture,
    ( ~ ~ v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(sK1,sK0) )).

tff(u3342,axiom,(
    ! [X1,X0] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u3341,axiom,(
    ! [X1,X0] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u3340,negated_conjecture,
    ( ~ ~ v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0) )).

tff(u3339,negated_conjecture,
    ( ~ ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) )).

tff(u3338,axiom,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) ) )).

tff(u3337,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)),X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) )).

tff(u3336,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k3_xboole_0(u1_struct_0(X0),X1)),X0)
      | k3_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_xboole_0(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k3_xboole_0(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) )).

tff(u3335,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k3_xboole_0(X1,u1_struct_0(X0))),X0)
      | k3_xboole_0(X1,u1_struct_0(X0)) = k2_pre_topc(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k3_xboole_0(X1,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ) )).

tff(u3334,axiom,(
    ! [X1,X0] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u3333,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u3332,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (9645)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (9648)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (9646)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (9647)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (9653)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (9644)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (9657)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (9655)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (9656)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (9655)Refutation not found, incomplete strategy% (9655)------------------------------
% 0.22/0.49  % (9655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9655)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9655)Memory used [KB]: 10746
% 0.22/0.49  % (9655)Time elapsed: 0.074 s
% 0.22/0.49  % (9655)------------------------------
% 0.22/0.49  % (9655)------------------------------
% 0.22/0.50  % (9651)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (9660)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (9659)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (9654)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (9658)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (9650)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (9649)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (9652)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (9661)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.54/0.59  % SZS status CounterSatisfiable for theBenchmark
% 1.54/0.59  % (9660)# SZS output start Saturation.
% 1.54/0.59  tff(u3444,negated_conjecture,
% 1.54/0.59      ((~(sK1 != k2_pre_topc(sK0,sK1))) | (sK1 != k2_pre_topc(sK0,sK1)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3443,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3442,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3441,axiom,
% 1.54/0.59      (![X5, X6] : ((k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X5)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3440,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3439,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3438,axiom,
% 1.54/0.59      (![X3, X2] : ((k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3437,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3436,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3435,axiom,
% 1.54/0.59      (![X5, X6] : ((k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k4_xboole_0(X5,X6),X5)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3434,axiom,
% 1.54/0.59      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3433,axiom,
% 1.54/0.59      (![X1] : ((k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3432,axiom,
% 1.54/0.59      (![X7, X8] : ((k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X8,X7))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3431,axiom,
% 1.54/0.59      (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3430,axiom,
% 1.54/0.59      (![X5, X7, X6] : ((k4_xboole_0(k4_xboole_0(X5,X6),X7) = k7_subset_1(X5,k4_xboole_0(X5,X6),X7))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3429,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3428,axiom,
% 1.54/0.59      (![X5, X6] : ((k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3427,axiom,
% 1.54/0.59      (![X69, X71, X70] : ((k4_xboole_0(k4_xboole_0(k3_xboole_0(X69,X70),X70),X71) = k7_subset_1(k4_xboole_0(k3_xboole_0(X69,X70),X69),k4_xboole_0(k3_xboole_0(X69,X70),X70),X71))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3426,axiom,
% 1.54/0.59      (![X27, X28] : ((k4_xboole_0(k4_xboole_0(k3_xboole_0(X27,X28),X28),k4_xboole_0(k3_xboole_0(X27,X28),X27)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X27,X28),X28),k3_xboole_0(X27,X28)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3425,axiom,
% 1.54/0.59      (![X46, X47] : ((k5_xboole_0(k4_xboole_0(k3_xboole_0(X46,X47),X47),k4_xboole_0(k3_xboole_0(X46,X47),X46)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X46,X47),X47),k3_xboole_0(X46,X47)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3424,axiom,
% 1.54/0.59      (![X75, X77, X76] : ((k4_xboole_0(k4_xboole_0(k3_xboole_0(X75,X76),X75),X77) = k7_subset_1(k4_xboole_0(k3_xboole_0(X75,X76),X76),k4_xboole_0(k3_xboole_0(X75,X76),X75),X77))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3423,axiom,
% 1.54/0.59      (![X16, X17] : ((k4_xboole_0(k4_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X16,X17),X16),k4_xboole_0(k3_xboole_0(X16,X17),X17)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3422,axiom,
% 1.54/0.59      (![X25, X24] : ((k4_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),X24),k3_xboole_0(X24,X25)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),X24),k4_xboole_0(k3_xboole_0(X24,X25),X25)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3421,axiom,
% 1.54/0.59      (![X11, X10] : ((k4_xboole_0(k3_xboole_0(X10,X11),X10) = k4_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X10,X11)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3420,axiom,
% 1.54/0.59      (![X16, X17] : ((k4_xboole_0(k3_xboole_0(X17,X16),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X17,X16),X17))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3419,axiom,
% 1.54/0.59      (![X3, X2] : ((k4_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k3_xboole_0(X2,X3),X2))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3418,axiom,
% 1.54/0.59      (![X20, X19] : ((k4_xboole_0(k3_xboole_0(X20,X19),X19) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X20,X19)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3417,axiom,
% 1.54/0.59      (![X23, X24] : ((k4_xboole_0(k3_xboole_0(X24,X23),X23) = k4_xboole_0(k3_xboole_0(X24,X23),k3_xboole_0(X23,X24)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3416,axiom,
% 1.54/0.59      (![X25, X24] : ((k4_xboole_0(k3_xboole_0(X24,X25),X25) = k3_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(k3_xboole_0(X24,X25),X24)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3415,axiom,
% 1.54/0.59      (![X1, X2] : ((k4_xboole_0(k3_xboole_0(X2,X1),X2) = k3_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(k3_xboole_0(X2,X1),X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3414,axiom,
% 1.54/0.59      (![X15, X14] : ((k4_xboole_0(k3_xboole_0(X14,X15),X15) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X14,X15),X15),k4_xboole_0(k3_xboole_0(X14,X15),X14)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3413,axiom,
% 1.54/0.59      (![X32, X33] : ((k4_xboole_0(k3_xboole_0(X32,X33),X33) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X32,X33),X32),k4_xboole_0(k3_xboole_0(X32,X33),X33)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3412,axiom,
% 1.54/0.59      (![X55, X54] : ((k4_xboole_0(k3_xboole_0(X54,X55),X54) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X54,X55),X55),k4_xboole_0(k3_xboole_0(X54,X55),X54)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3411,axiom,
% 1.54/0.59      (![X58, X59] : ((k4_xboole_0(k3_xboole_0(X58,X59),X58) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X58,X59),X58),k4_xboole_0(k3_xboole_0(X58,X59),X59)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3410,axiom,
% 1.54/0.59      (![X38, X39] : ((k4_xboole_0(k3_xboole_0(X38,X39),X39) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X38,X39),X38),k3_xboole_0(X38,X39)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3409,axiom,
% 1.54/0.59      (![X93, X94] : ((k4_xboole_0(k3_xboole_0(X93,X94),X93) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X93,X94),X94),k3_xboole_0(X93,X94)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3408,axiom,
% 1.54/0.59      (![X1, X0] : ((k4_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3407,axiom,
% 1.54/0.59      (![X20, X19] : ((k4_xboole_0(k3_xboole_0(X20,X19),X20) = k5_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3406,axiom,
% 1.54/0.59      (![X18, X17] : ((k4_xboole_0(k3_xboole_0(X18,X17),X17) = k5_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X17,X18)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3405,axiom,
% 1.54/0.59      (![X11, X13, X12] : ((k4_xboole_0(k3_xboole_0(X11,X12),X13) = k7_subset_1(X11,k3_xboole_0(X11,X12),X13))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3404,axiom,
% 1.54/0.59      (![X16, X15, X14] : ((k4_xboole_0(k3_xboole_0(X14,X15),X16) = k7_subset_1(X15,k3_xboole_0(X14,X15),X16))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3403,axiom,
% 1.54/0.59      (![X20, X22, X21] : ((k4_xboole_0(k3_xboole_0(X20,X21),X22) = k7_subset_1(k3_xboole_0(X21,X20),k3_xboole_0(X20,X21),X22))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3402,negated_conjecture,
% 1.54/0.59      (k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1))).
% 1.54/0.59  
% 1.54/0.59  tff(u3401,negated_conjecture,
% 1.54/0.59      (k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1))).
% 1.54/0.59  
% 1.54/0.59  tff(u3400,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3399,axiom,
% 1.54/0.59      (![X3, X2] : ((k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X2)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3398,axiom,
% 1.54/0.59      (![X3, X2] : ((k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3397,axiom,
% 1.54/0.59      (![X20, X21] : ((k3_xboole_0(X21,X20) = k4_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(k3_xboole_0(X20,X21),X21)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3396,axiom,
% 1.54/0.59      (![X25, X24] : ((k3_xboole_0(X25,X24) = k4_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(k3_xboole_0(X24,X25),X24)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3395,axiom,
% 1.54/0.59      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3394,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3393,axiom,
% 1.54/0.59      (![X7, X6] : ((k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X7,X6),X6))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3392,axiom,
% 1.54/0.59      (![X5, X4] : ((k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X4,X5)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3391,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3390,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3389,axiom,
% 1.54/0.59      (![X27, X28] : ((k3_xboole_0(X27,X28) = k3_xboole_0(k3_xboole_0(X28,X27),k3_xboole_0(X27,X28)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3388,axiom,
% 1.54/0.59      (![X5, X4] : ((k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X5,X4)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3387,axiom,
% 1.54/0.59      (![X9, X10] : ((k3_xboole_0(X10,X9) = k3_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,X10)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3386,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3385,axiom,
% 1.54/0.59      (![X7, X8] : ((k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3384,axiom,
% 1.54/0.59      (![X16, X17] : ((k3_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),X16)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3383,axiom,
% 1.54/0.59      (![X16, X17] : ((k3_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),X17)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3382,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3381,axiom,
% 1.54/0.59      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3380,axiom,
% 1.54/0.59      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3379,axiom,
% 1.54/0.59      (![X7, X6] : ((k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,X6))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3378,axiom,
% 1.54/0.59      (![X9, X8] : ((k3_xboole_0(k3_xboole_0(X8,X9),X8) = k3_xboole_0(X9,X8))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3377,axiom,
% 1.54/0.59      (![X13, X14] : ((k4_xboole_0(k3_xboole_0(X14,X13),X13) = k5_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X14,X13)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3376,axiom,
% 1.54/0.59      (![X0] : ((k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3375,axiom,
% 1.54/0.59      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3374,axiom,
% 1.54/0.59      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3373,negated_conjecture,
% 1.54/0.59      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3372,negated_conjecture,
% 1.54/0.59      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3371,negated_conjecture,
% 1.54/0.59      (sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3370,negated_conjecture,
% 1.54/0.59      (sK1 = k3_xboole_0(u1_struct_0(sK0),sK1))).
% 1.54/0.59  
% 1.54/0.59  tff(u3369,axiom,
% 1.54/0.59      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k4_xboole_0(X4,X5) = k7_subset_1(X3,X4,X5)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3368,axiom,
% 1.54/0.59      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3367,axiom,
% 1.54/0.59      (![X1, X2] : ((~r1_tarski(X1,u1_struct_0(X2)) | (k2_pre_topc(X2,X1) = X1) | ~l1_pre_topc(X2) | ~v4_pre_topc(X1,X2))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3366,axiom,
% 1.54/0.59      (![X1, X0] : ((r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3365,axiom,
% 1.54/0.59      (![X0] : (r1_tarski(X0,X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3364,axiom,
% 1.54/0.59      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3363,axiom,
% 1.54/0.59      (![X5, X4] : (r1_tarski(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3362,axiom,
% 1.54/0.59      (![X13, X12] : (r1_tarski(k4_xboole_0(k3_xboole_0(X12,X13),X13),k4_xboole_0(k3_xboole_0(X12,X13),X12))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3361,axiom,
% 1.54/0.59      (![X44, X45] : (r1_tarski(k4_xboole_0(k3_xboole_0(X44,X45),X44),k4_xboole_0(k3_xboole_0(X44,X45),X45))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3360,axiom,
% 1.54/0.59      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3359,axiom,
% 1.54/0.59      (![X1, X0] : (r1_tarski(k3_xboole_0(X1,X0),X0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3358,axiom,
% 1.54/0.59      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3357,axiom,
% 1.54/0.59      (![X13, X14] : (r1_tarski(k3_xboole_0(X13,X14),k3_xboole_0(X14,X13))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3356,negated_conjecture,
% 1.54/0.59      r1_tarski(sK1,sK1)).
% 1.54/0.59  
% 1.54/0.59  tff(u3355,negated_conjecture,
% 1.54/0.59      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.54/0.59  
% 1.54/0.59  tff(u3354,axiom,
% 1.54/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3353,axiom,
% 1.54/0.59      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k3_xboole_0(X2,X3) = X2))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3352,axiom,
% 1.54/0.59      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) = X1) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3351,axiom,
% 1.54/0.59      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3350,axiom,
% 1.54/0.59      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3349,negated_conjecture,
% 1.54/0.59      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.54/0.59  
% 1.54/0.59  tff(u3348,negated_conjecture,
% 1.54/0.59      l1_pre_topc(sK0)).
% 1.54/0.59  
% 1.54/0.59  tff(u3347,axiom,
% 1.54/0.59      (![X3, X4] : ((~v4_pre_topc(k4_xboole_0(u1_struct_0(X3),X4),X3) | ~l1_pre_topc(X3) | (k4_xboole_0(u1_struct_0(X3),X4) = k2_pre_topc(X3,k4_xboole_0(u1_struct_0(X3),X4))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3346,axiom,
% 1.54/0.59      (![X5, X6] : ((~v4_pre_topc(k3_xboole_0(u1_struct_0(X5),X6),X5) | ~l1_pre_topc(X5) | (k3_xboole_0(u1_struct_0(X5),X6) = k2_pre_topc(X5,k3_xboole_0(u1_struct_0(X5),X6))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3345,axiom,
% 1.54/0.59      (![X7, X8] : ((~v4_pre_topc(k3_xboole_0(X8,u1_struct_0(X7)),X7) | ~l1_pre_topc(X7) | (k3_xboole_0(X8,u1_struct_0(X7)) = k2_pre_topc(X7,k3_xboole_0(X8,u1_struct_0(X7)))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3344,axiom,
% 1.54/0.59      (![X0] : ((~v4_pre_topc(u1_struct_0(X0),X0) | (u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3343,negated_conjecture,
% 1.54/0.59      ((~~v4_pre_topc(sK1,sK0)) | ~v4_pre_topc(sK1,sK0))).
% 1.54/0.59  
% 1.54/0.59  tff(u3342,axiom,
% 1.54/0.59      (![X1, X0] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3341,axiom,
% 1.54/0.59      (![X1, X0] : ((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3340,negated_conjecture,
% 1.54/0.59      ((~~v3_pre_topc(sK1,sK0)) | ~v3_pre_topc(sK1,sK0))).
% 1.54/0.59  
% 1.54/0.59  tff(u3339,negated_conjecture,
% 1.54/0.59      ((~~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0))).
% 1.54/0.59  
% 1.54/0.59  tff(u3338,axiom,
% 1.54/0.59      (![X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)),X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | (u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3337,axiom,
% 1.54/0.59      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1)),X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3336,axiom,
% 1.54/0.59      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k3_xboole_0(u1_struct_0(X0),X1)),X0) | (k3_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_xboole_0(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(k3_xboole_0(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3335,axiom,
% 1.54/0.59      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k3_xboole_0(X1,u1_struct_0(X0))),X0) | (k3_xboole_0(X1,u1_struct_0(X0)) = k2_pre_topc(X0,k3_xboole_0(X1,u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(k3_xboole_0(X1,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3334,axiom,
% 1.54/0.59      (![X1, X0] : ((v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3333,axiom,
% 1.54/0.59      (![X0] : ((l1_struct_0(X0) | ~l1_pre_topc(X0))))).
% 1.54/0.59  
% 1.54/0.59  tff(u3332,negated_conjecture,
% 1.54/0.59      ((~v2_pre_topc(sK0)) | v2_pre_topc(sK0))).
% 1.54/0.59  
% 1.54/0.59  % (9660)# SZS output end Saturation.
% 1.54/0.59  % (9660)------------------------------
% 1.54/0.59  % (9660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (9660)Termination reason: Satisfiable
% 1.54/0.59  
% 1.54/0.59  % (9660)Memory used [KB]: 7419
% 1.54/0.59  % (9660)Time elapsed: 0.162 s
% 1.54/0.59  % (9660)------------------------------
% 1.54/0.59  % (9660)------------------------------
% 1.54/0.59  % (9643)Success in time 0.226 s
%------------------------------------------------------------------------------
