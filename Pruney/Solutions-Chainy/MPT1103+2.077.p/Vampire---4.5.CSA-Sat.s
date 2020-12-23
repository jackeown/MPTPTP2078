%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 1.68s
% Output     : Saturation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   90 (  90 expanded)
%              Number of leaves         :   90 (  90 expanded)
%              Depth                    :    0
%              Number of atoms          :  182 ( 182 expanded)
%              Number of equality atoms :  105 ( 105 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u1116,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u1115,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u1114,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )).

tff(u1113,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1112,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )
    | k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1111,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 )).

tff(u1110,axiom,(
    ! [X3,X4] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) )).

tff(u1109,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u1108,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X0] : k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) )).

tff(u1107,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X1] : k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0) )).

tff(u1106,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u1105,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u1104,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u1103,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u1102,axiom,
    ( k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) )).

tff(u1101,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 )).

tff(u1100,axiom,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u1099,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X1] : k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 )).

tff(u1098,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

tff(u1097,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u1096,axiom,(
    ! [X1] : k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = k4_subset_1(X1,X1,X1) )).

tff(u1095,axiom,(
    ! [X1,X3,X2] : k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)) = k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1)) )).

tff(u1094,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u1093,axiom,(
    ! [X1] : k4_subset_1(X1,k1_xboole_0,X1) = X1 )).

tff(u1092,axiom,(
    ! [X2] : k4_subset_1(X2,X2,X2) = k3_subset_1(X2,k7_subset_1(k1_xboole_0,k1_xboole_0,X2)) )).

tff(u1091,axiom,(
    ! [X7,X6] : k4_subset_1(X6,X6,X6) = k3_subset_1(X6,k7_subset_1(X7,k1_xboole_0,X6)) )).

tff(u1090,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )).

tff(u1089,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)) )).

tff(u1088,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ! [X0] : k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) )).

tff(u1087,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k4_subset_1(sK1,sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

tff(u1086,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u1085,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1084,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) )).

tff(u1083,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

tff(u1082,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) )).

tff(u1081,axiom,(
    ! [X3,X2] : k7_subset_1(X2,k1_xboole_0,X3) = k7_subset_1(k1_xboole_0,k1_xboole_0,X3) )).

tff(u1080,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u1079,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X4] : k7_subset_1(u1_struct_0(sK0),sK1,X4) = k7_subset_1(sK1,sK1,X4) )).

tff(u1078,axiom,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

tff(u1077,negated_conjecture,
    ( u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

tff(u1076,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u1075,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u1074,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u1073,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u1072,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)
    | sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

tff(u1071,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u1070,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u1069,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) )).

tff(u1068,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) )).

tff(u1067,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X1,X1,X0) ) )).

tff(u1066,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3) ) )).

tff(u1065,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k4_subset_1(X4,X4,X3) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)) ) )).

tff(u1064,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u1063,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,k1_xboole_0,X0) = X0 ) )).

tff(u1062,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u1061,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)) ) )).

tff(u1060,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X2)) ) )).

tff(u1059,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1058,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1)) )).

tff(u1057,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1056,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1055,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1054,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0))
        | ~ r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0))
        | k7_subset_1(X0,X0,k1_xboole_0) = X0 ) )).

tff(u1053,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1)) )).

tff(u1052,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) )).

tff(u1051,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0))) )).

tff(u1050,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u1049,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u1048,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1047,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u1046,axiom,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) )).

tff(u1045,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) )).

tff(u1044,negated_conjecture,
    ( ~ ~ r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)) )).

tff(u1043,negated_conjecture,
    ( ~ ~ r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))
    | ~ r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) )).

tff(u1042,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(X0,k1_xboole_0,X0) = X0 ) )).

tff(u1041,axiom,(
    ! [X9,X8,X10] :
      ( ~ r1_tarski(k3_subset_1(X8,k7_subset_1(X10,k1_xboole_0,X8)),k7_subset_1(X9,k1_xboole_0,X8))
      | ~ m1_subset_1(k7_subset_1(X9,k1_xboole_0,X8),k1_zfmisc_1(X8))
      | k7_subset_1(X9,k1_xboole_0,X8) = X8 ) )).

tff(u1040,axiom,(
    ! [X0] :
      ( ~ r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(X0,k1_xboole_0,X0) = X0 ) )).

tff(u1039,axiom,(
    ! [X0] :
      ( ~ r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0 ) )).

tff(u1038,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(k4_subset_1(X2,X2,X2),k7_subset_1(X3,k1_xboole_0,X2))
      | ~ m1_subset_1(k7_subset_1(X3,k1_xboole_0,X2),k1_zfmisc_1(X2))
      | k7_subset_1(X3,k1_xboole_0,X2) = X2 ) )).

tff(u1037,negated_conjecture,
    ( ~ ~ r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0) )).

tff(u1036,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k7_subset_1(X1,k1_xboole_0,X1),k4_subset_1(X1,X1,X1))
      | k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X1)
      | ~ m1_subset_1(k7_subset_1(X1,k1_xboole_0,X1),k1_zfmisc_1(X1)) ) )).

tff(u1035,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1))
      | k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)
      | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(X1)) ) )).

tff(u1034,axiom,(
    ! [X5,X4] :
      ( ~ r1_tarski(k7_subset_1(X5,k1_xboole_0,X4),k4_subset_1(X4,X4,X4))
      | k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X4)
      | ~ m1_subset_1(k7_subset_1(X5,k1_xboole_0,X4),k1_zfmisc_1(X4)) ) )).

tff(u1033,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)))
      | k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0)
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) ) )).

tff(u1032,axiom,(
    ! [X11,X13,X12] :
      ( ~ r1_tarski(k7_subset_1(X12,k1_xboole_0,X11),k3_subset_1(X11,k7_subset_1(X13,k1_xboole_0,X11)))
      | k1_xboole_0 = k7_subset_1(X12,k1_xboole_0,X11)
      | ~ m1_subset_1(k7_subset_1(X12,k1_xboole_0,X11),k1_zfmisc_1(X11)) ) )).

tff(u1031,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u1030,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1)
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1) )).

tff(u1029,axiom,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))) ) )).

tff(u1028,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u1027,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (19156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.49  % (19137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (19137)Refutation not found, incomplete strategy% (19137)------------------------------
% 0.21/0.49  % (19137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19156)Refutation not found, incomplete strategy% (19156)------------------------------
% 0.21/0.50  % (19156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19137)Memory used [KB]: 6396
% 0.21/0.50  % (19137)Time elapsed: 0.078 s
% 0.21/0.50  % (19137)------------------------------
% 0.21/0.50  % (19137)------------------------------
% 0.21/0.51  % (19156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19156)Memory used [KB]: 6524
% 0.21/0.51  % (19156)Time elapsed: 0.089 s
% 0.21/0.51  % (19156)------------------------------
% 0.21/0.51  % (19156)------------------------------
% 0.21/0.51  % (19142)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (19142)Refutation not found, incomplete strategy% (19142)------------------------------
% 0.21/0.51  % (19142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19145)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (19130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (19154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (19147)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (19134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (19153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (19142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19142)Memory used [KB]: 10618
% 0.21/0.53  % (19142)Time elapsed: 0.094 s
% 0.21/0.53  % (19142)------------------------------
% 0.21/0.53  % (19142)------------------------------
% 0.21/0.53  % (19134)Refutation not found, incomplete strategy% (19134)------------------------------
% 0.21/0.53  % (19134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19134)Memory used [KB]: 6396
% 0.21/0.53  % (19134)Time elapsed: 0.125 s
% 0.21/0.53  % (19134)------------------------------
% 0.21/0.53  % (19134)------------------------------
% 0.21/0.54  % (19155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19135)Refutation not found, incomplete strategy% (19135)------------------------------
% 0.21/0.54  % (19135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19135)Memory used [KB]: 6524
% 0.21/0.54  % (19135)Time elapsed: 0.092 s
% 0.21/0.54  % (19135)------------------------------
% 0.21/0.54  % (19135)------------------------------
% 0.21/0.54  % (19160)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19131)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (19130)Refutation not found, incomplete strategy% (19130)------------------------------
% 0.21/0.54  % (19130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19143)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (19148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (19130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19130)Memory used [KB]: 1663
% 0.21/0.54  % (19130)Time elapsed: 0.123 s
% 0.21/0.54  % (19130)------------------------------
% 0.21/0.54  % (19130)------------------------------
% 0.21/0.54  % (19133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (19150)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (19154)Refutation not found, incomplete strategy% (19154)------------------------------
% 0.21/0.54  % (19154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19154)Memory used [KB]: 1791
% 0.21/0.54  % (19154)Time elapsed: 0.130 s
% 0.21/0.54  % (19154)------------------------------
% 0.21/0.54  % (19154)------------------------------
% 0.21/0.54  % (19146)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (19146)Refutation not found, incomplete strategy% (19146)------------------------------
% 0.21/0.54  % (19146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (19146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19146)Memory used [KB]: 6140
% 0.21/0.54  % (19153)Refutation not found, incomplete strategy% (19153)------------------------------
% 0.21/0.54  % (19153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19146)Time elapsed: 0.004 s
% 0.21/0.54  % (19146)------------------------------
% 0.21/0.54  % (19146)------------------------------
% 0.21/0.55  % (19139)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (19153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19153)Memory used [KB]: 10746
% 0.21/0.55  % (19153)Time elapsed: 0.097 s
% 0.21/0.55  % (19153)------------------------------
% 0.21/0.55  % (19153)------------------------------
% 0.21/0.55  % (19158)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (19149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (19132)Refutation not found, incomplete strategy% (19132)------------------------------
% 0.21/0.55  % (19132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19132)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19132)Memory used [KB]: 10746
% 0.21/0.55  % (19132)Time elapsed: 0.122 s
% 0.21/0.55  % (19132)------------------------------
% 0.21/0.55  % (19132)------------------------------
% 0.21/0.55  % (19139)Refutation not found, incomplete strategy% (19139)------------------------------
% 0.21/0.55  % (19139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19139)Memory used [KB]: 10746
% 0.21/0.55  % (19139)Time elapsed: 0.138 s
% 0.21/0.55  % (19139)------------------------------
% 0.21/0.55  % (19139)------------------------------
% 0.21/0.55  % (19148)Refutation not found, incomplete strategy% (19148)------------------------------
% 0.21/0.55  % (19148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19148)Memory used [KB]: 10618
% 0.21/0.55  % (19148)Time elapsed: 0.136 s
% 0.21/0.55  % (19148)------------------------------
% 0.21/0.55  % (19148)------------------------------
% 0.21/0.55  % (19144)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (19151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19141)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (19141)Refutation not found, incomplete strategy% (19141)------------------------------
% 0.21/0.55  % (19141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (19136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.56  % (19152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.56  % (19141)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (19141)Memory used [KB]: 10618
% 1.57/0.56  % (19141)Time elapsed: 0.139 s
% 1.57/0.56  % (19141)------------------------------
% 1.57/0.56  % (19141)------------------------------
% 1.57/0.56  % (19152)Refutation not found, incomplete strategy% (19152)------------------------------
% 1.57/0.56  % (19152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (19152)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (19152)Memory used [KB]: 1791
% 1.57/0.56  % (19152)Time elapsed: 0.154 s
% 1.57/0.56  % (19152)------------------------------
% 1.57/0.56  % (19152)------------------------------
% 1.57/0.56  % (19157)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.57  % (19140)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.57  % (19140)Refutation not found, incomplete strategy% (19140)------------------------------
% 1.57/0.57  % (19140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (19140)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (19140)Memory used [KB]: 10618
% 1.57/0.57  % (19140)Time elapsed: 0.158 s
% 1.57/0.57  % (19140)------------------------------
% 1.57/0.57  % (19140)------------------------------
% 1.57/0.57  % (19157)Refutation not found, incomplete strategy% (19157)------------------------------
% 1.57/0.57  % (19157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (19157)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (19157)Memory used [KB]: 10874
% 1.57/0.57  % (19157)Time elapsed: 0.162 s
% 1.57/0.57  % (19157)------------------------------
% 1.57/0.57  % (19157)------------------------------
% 1.68/0.57  % (19133)Refutation not found, incomplete strategy% (19133)------------------------------
% 1.68/0.57  % (19133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.57  % (19133)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.57  
% 1.68/0.57  % (19133)Memory used [KB]: 11001
% 1.68/0.57  % (19133)Time elapsed: 0.149 s
% 1.68/0.57  % (19133)------------------------------
% 1.68/0.57  % (19133)------------------------------
% 1.68/0.58  % (19151)Refutation not found, incomplete strategy% (19151)------------------------------
% 1.68/0.58  % (19151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (19151)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (19151)Memory used [KB]: 11001
% 1.68/0.58  % (19151)Time elapsed: 0.154 s
% 1.68/0.58  % (19151)------------------------------
% 1.68/0.58  % (19151)------------------------------
% 1.68/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.68/0.58  % (19147)# SZS output start Saturation.
% 1.68/0.58  tff(u1116,negated_conjecture,
% 1.68/0.58      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1115,negated_conjecture,
% 1.68/0.58      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1114,negated_conjecture,
% 1.68/0.58      ((~(sK1 != k7_subset_1(sK1,sK1,k1_xboole_0))) | (sK1 != k7_subset_1(sK1,sK1,k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1113,negated_conjecture,
% 1.68/0.58      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1112,negated_conjecture,
% 1.68/0.58      ((~(k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1111,axiom,
% 1.68/0.58      (![X0] : ((k5_xboole_0(X0,X0) = k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1110,axiom,
% 1.68/0.58      (![X3, X4] : ((k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1109,axiom,
% 1.68/0.58      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1108,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X0] : ((k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1107,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X1] : ((k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1106,negated_conjecture,
% 1.68/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1105,negated_conjecture,
% 1.68/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1104,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1103,axiom,
% 1.68/0.58      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1102,axiom,
% 1.68/0.58      ((~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1101,axiom,
% 1.68/0.58      (![X0] : ((k3_tarski(k1_zfmisc_1(X0)) = X0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1100,axiom,
% 1.68/0.58      (![X0] : ((k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1099,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X1] : ((k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1098,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1097,axiom,
% 1.68/0.58      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1096,axiom,
% 1.68/0.58      (![X1] : ((k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = k4_subset_1(X1,X1,X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1095,axiom,
% 1.68/0.58      (![X1, X3, X2] : ((k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)) = k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1094,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X0] : ((k4_subset_1(X0,X0,k1_xboole_0) = X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1093,axiom,
% 1.68/0.58      (![X1] : ((k4_subset_1(X1,k1_xboole_0,X1) = X1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1092,axiom,
% 1.68/0.58      (![X2] : ((k4_subset_1(X2,X2,X2) = k3_subset_1(X2,k7_subset_1(k1_xboole_0,k1_xboole_0,X2)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1091,axiom,
% 1.68/0.58      (![X7, X6] : ((k4_subset_1(X6,X6,X6) = k3_subset_1(X6,k7_subset_1(X7,k1_xboole_0,X6)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1090,axiom,
% 1.68/0.58      (![X0] : ((k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1089,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1088,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)))) | (![X0] : ((k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1087,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1086,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1085,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1084,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1083,negated_conjecture,
% 1.68/0.58      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1082,axiom,
% 1.68/0.58      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1081,axiom,
% 1.68/0.58      (![X3, X2] : ((k7_subset_1(X2,k1_xboole_0,X3) = k7_subset_1(k1_xboole_0,k1_xboole_0,X3))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1080,axiom,
% 1.68/0.58      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1079,negated_conjecture,
% 1.68/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X4] : ((k7_subset_1(u1_struct_0(sK0),sK1,X4) = k7_subset_1(sK1,sK1,X4)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1078,axiom,
% 1.68/0.58      (![X0] : ((k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1077,negated_conjecture,
% 1.68/0.58      ((~(u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1))) | (u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1076,negated_conjecture,
% 1.68/0.58      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1075,negated_conjecture,
% 1.68/0.58      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1074,negated_conjecture,
% 1.68/0.58      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1073,negated_conjecture,
% 1.68/0.58      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1072,negated_conjecture,
% 1.68/0.58      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))) | (sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1071,negated_conjecture,
% 1.68/0.58      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1070,axiom,
% 1.68/0.58      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1069,axiom,
% 1.68/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1068,axiom,
% 1.68/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1067,axiom,
% 1.68/0.58      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X1,X1,X0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1066,axiom,
% 1.68/0.58      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1065,axiom,
% 1.68/0.58      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k4_subset_1(X4,X4,X3) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1064,axiom,
% 1.68/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1063,axiom,
% 1.68/0.58      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k4_subset_1(X1,k1_xboole_0,X0) = X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1062,axiom,
% 1.68/0.58      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1061,negated_conjecture,
% 1.68/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1060,negated_conjecture,
% 1.68/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X2)))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1059,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1058,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1))) | ~m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1057,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1056,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : (~m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1055,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1054,axiom,
% 1.68/0.58      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X0] : ((~m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) | ~r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) | (k7_subset_1(X0,X0,k1_xboole_0) = X0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1053,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1052,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1051,negated_conjecture,
% 1.68/0.58      ((~~m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1050,axiom,
% 1.68/0.58      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1049,axiom,
% 1.68/0.58      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1048,negated_conjecture,
% 1.68/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1047,axiom,
% 1.68/0.58      (![X1, X0] : ((~r1_tarski(X1,k3_subset_1(X0,X1)) | (k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1046,axiom,
% 1.68/0.58      (![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1045,axiom,
% 1.68/0.58      (![X1, X0] : ((~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | (X0 = X1))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1044,negated_conjecture,
% 1.68/0.58      ((~~r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))) | ~r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1043,negated_conjecture,
% 1.68/0.58      ((~~r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | ~r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1042,axiom,
% 1.68/0.58      (![X1, X0] : ((~r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(X0,k1_xboole_0,X0) = X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1041,axiom,
% 1.68/0.58      (![X9, X8, X10] : ((~r1_tarski(k3_subset_1(X8,k7_subset_1(X10,k1_xboole_0,X8)),k7_subset_1(X9,k1_xboole_0,X8)) | ~m1_subset_1(k7_subset_1(X9,k1_xboole_0,X8),k1_zfmisc_1(X8)) | (k7_subset_1(X9,k1_xboole_0,X8) = X8))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1040,axiom,
% 1.68/0.58      (![X0] : ((~r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(X0,k1_xboole_0,X0) = X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1039,axiom,
% 1.68/0.58      (![X0] : ((~r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1038,axiom,
% 1.68/0.58      (![X3, X2] : ((~r1_tarski(k4_subset_1(X2,X2,X2),k7_subset_1(X3,k1_xboole_0,X2)) | ~m1_subset_1(k7_subset_1(X3,k1_xboole_0,X2),k1_zfmisc_1(X2)) | (k7_subset_1(X3,k1_xboole_0,X2) = X2))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1037,negated_conjecture,
% 1.68/0.58      ((~~r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0)) | ~r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0))).
% 1.68/0.58  
% 1.68/0.58  tff(u1036,axiom,
% 1.68/0.58      (![X1] : ((~r1_tarski(k7_subset_1(X1,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) | (k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X1)) | ~m1_subset_1(k7_subset_1(X1,k1_xboole_0,X1),k1_zfmisc_1(X1)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1035,axiom,
% 1.68/0.58      (![X1] : ((~r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) | (k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(X1)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1034,axiom,
% 1.68/0.58      (![X5, X4] : ((~r1_tarski(k7_subset_1(X5,k1_xboole_0,X4),k4_subset_1(X4,X4,X4)) | (k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X4)) | ~m1_subset_1(k7_subset_1(X5,k1_xboole_0,X4),k1_zfmisc_1(X4)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1033,axiom,
% 1.68/0.58      (![X1, X0] : ((~r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0))) | (k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1032,axiom,
% 1.68/0.58      (![X11, X13, X12] : ((~r1_tarski(k7_subset_1(X12,k1_xboole_0,X11),k3_subset_1(X11,k7_subset_1(X13,k1_xboole_0,X11))) | (k1_xboole_0 = k7_subset_1(X12,k1_xboole_0,X11)) | ~m1_subset_1(k7_subset_1(X12,k1_xboole_0,X11),k1_zfmisc_1(X11)))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1031,axiom,
% 1.68/0.58      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 1.68/0.58  
% 1.68/0.58  tff(u1030,negated_conjecture,
% 1.68/0.58      ((~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1)) | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1))).
% 1.68/0.58  
% 1.68/0.58  tff(u1029,axiom,
% 1.68/0.58      (![X1] : ((~l1_struct_0(X1) | (u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1028,axiom,
% 1.68/0.58      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 1.68/0.58  
% 1.68/0.58  tff(u1027,negated_conjecture,
% 1.68/0.58      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 1.68/0.58  
% 1.68/0.58  % (19147)# SZS output end Saturation.
% 1.68/0.58  % (19147)------------------------------
% 1.68/0.58  % (19147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (19147)Termination reason: Satisfiable
% 1.68/0.58  
% 1.68/0.58  % (19147)Memory used [KB]: 11385
% 1.68/0.58  % (19147)Time elapsed: 0.173 s
% 1.68/0.58  % (19147)------------------------------
% 1.68/0.58  % (19147)------------------------------
% 1.68/0.58  % (19161)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.58  % (19129)Success in time 0.216 s
%------------------------------------------------------------------------------
