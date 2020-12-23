%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
tff(u1117,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u1116,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u1115,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )).

tff(u1114,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1113,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )
    | k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1112,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 )).

tff(u1111,axiom,(
    ! [X3,X4] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) )).

tff(u1110,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u1109,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X0] : k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) )).

tff(u1108,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X1] : k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0) )).

tff(u1107,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u1106,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u1105,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u1104,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u1103,axiom,
    ( k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) )).

tff(u1102,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 )).

tff(u1101,axiom,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u1100,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X1] : k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 )).

tff(u1099,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

tff(u1098,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u1097,axiom,(
    ! [X1] : k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = k4_subset_1(X1,X1,X1) )).

tff(u1096,axiom,(
    ! [X1,X3,X2] : k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)) = k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1)) )).

tff(u1095,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_setfam_1(k1_zfmisc_1(k1_xboole_0))
    | ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u1094,axiom,(
    ! [X1] : k4_subset_1(X1,k1_xboole_0,X1) = X1 )).

tff(u1093,axiom,(
    ! [X2] : k4_subset_1(X2,X2,X2) = k3_subset_1(X2,k7_subset_1(k1_xboole_0,k1_xboole_0,X2)) )).

tff(u1092,axiom,(
    ! [X7,X6] : k4_subset_1(X6,X6,X6) = k3_subset_1(X6,k7_subset_1(X7,k1_xboole_0,X6)) )).

tff(u1091,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )).

tff(u1090,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)) )).

tff(u1089,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ! [X0] : k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) )).

tff(u1088,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k4_subset_1(sK1,sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

tff(u1087,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u1086,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) )).

tff(u1085,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) )).

tff(u1084,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

tff(u1083,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) )).

tff(u1082,axiom,(
    ! [X3,X2] : k7_subset_1(X2,k1_xboole_0,X3) = k7_subset_1(k1_xboole_0,k1_xboole_0,X3) )).

tff(u1081,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u1080,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X4] : k7_subset_1(u1_struct_0(sK0),sK1,X4) = k7_subset_1(sK1,sK1,X4) )).

tff(u1079,axiom,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

tff(u1078,negated_conjecture,
    ( u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

tff(u1077,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u1076,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u1075,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

tff(u1074,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u1073,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)
    | sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

tff(u1072,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u1071,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u1070,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) )).

tff(u1069,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) )).

tff(u1068,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X1,X1,X0) ) )).

tff(u1067,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3) ) )).

tff(u1066,axiom,(
    ! [X3,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | k4_subset_1(X4,X4,X3) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)) ) )).

tff(u1065,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u1064,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_subset_1(X1,k1_xboole_0,X0) = X0 ) )).

tff(u1063,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u1062,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)) ) )).

tff(u1061,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X2)) ) )).

tff(u1060,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1059,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1)) )).

tff(u1058,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1057,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1056,negated_conjecture,
    ( ~ ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1055,axiom,
    ( k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ! [X0] :
        ( ~ m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0))
        | ~ r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0))
        | k7_subset_1(X0,X0,k1_xboole_0) = X0 ) )).

tff(u1054,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1)) )).

tff(u1053,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) )).

% (28266)Refutation not found, incomplete strategy% (28266)------------------------------
% (28266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u1052,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0))) )).

tff(u1051,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

% (28266)Termination reason: Refutation not found, incomplete strategy

tff(u1050,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u1049,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

% (28266)Memory used [KB]: 10618
% (28266)Time elapsed: 0.150 s
% (28266)------------------------------
% (28266)------------------------------
tff(u1048,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u1047,axiom,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) )).

tff(u1046,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) )).

tff(u1045,negated_conjecture,
    ( ~ ~ r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)) )).

tff(u1044,negated_conjecture,
    ( ~ ~ r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))
    | ~ r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) )).

tff(u1043,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(X0,k1_xboole_0,X0) = X0 ) )).

tff(u1042,axiom,(
    ! [X9,X8,X10] :
      ( ~ r1_tarski(k3_subset_1(X8,k7_subset_1(X10,k1_xboole_0,X8)),k7_subset_1(X9,k1_xboole_0,X8))
      | ~ m1_subset_1(k7_subset_1(X9,k1_xboole_0,X8),k1_zfmisc_1(X8))
      | k7_subset_1(X9,k1_xboole_0,X8) = X8 ) )).

tff(u1041,axiom,(
    ! [X0] :
      ( ~ r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(X0,k1_xboole_0,X0) = X0 ) )).

tff(u1040,axiom,(
    ! [X0] :
      ( ~ r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0))
      | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0))
      | k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0 ) )).

tff(u1039,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(k4_subset_1(X2,X2,X2),k7_subset_1(X3,k1_xboole_0,X2))
      | ~ m1_subset_1(k7_subset_1(X3,k1_xboole_0,X2),k1_zfmisc_1(X2))
      | k7_subset_1(X3,k1_xboole_0,X2) = X2 ) )).

tff(u1038,negated_conjecture,
    ( ~ ~ r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0) )).

tff(u1037,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k7_subset_1(X1,k1_xboole_0,X1),k4_subset_1(X1,X1,X1))
      | k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X1)
      | ~ m1_subset_1(k7_subset_1(X1,k1_xboole_0,X1),k1_zfmisc_1(X1)) ) )).

tff(u1036,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1))
      | k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)
      | ~ m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(X1)) ) )).

tff(u1035,axiom,(
    ! [X5,X4] :
      ( ~ r1_tarski(k7_subset_1(X5,k1_xboole_0,X4),k4_subset_1(X4,X4,X4))
      | k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X4)
      | ~ m1_subset_1(k7_subset_1(X5,k1_xboole_0,X4),k1_zfmisc_1(X4)) ) )).

tff(u1034,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)))
      | k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0)
      | ~ m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) ) )).

tff(u1033,axiom,(
    ! [X11,X13,X12] :
      ( ~ r1_tarski(k7_subset_1(X12,k1_xboole_0,X11),k3_subset_1(X11,k7_subset_1(X13,k1_xboole_0,X11)))
      | k1_xboole_0 = k7_subset_1(X12,k1_xboole_0,X11)
      | ~ m1_subset_1(k7_subset_1(X12,k1_xboole_0,X11),k1_zfmisc_1(X11)) ) )).

tff(u1032,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u1031,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1)
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1) )).

tff(u1030,axiom,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))) ) )).

tff(u1029,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u1028,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

% (28272)Refutation not found, incomplete strategy% (28272)------------------------------
% (28272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28263)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (28263)Refutation not found, incomplete strategy% (28263)------------------------------
% 0.21/0.52  % (28263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28279)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (28271)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (28263)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28263)Memory used [KB]: 10746
% 0.21/0.52  % (28263)Time elapsed: 0.094 s
% 0.21/0.52  % (28263)------------------------------
% 0.21/0.52  % (28263)------------------------------
% 0.21/0.52  % (28261)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28278)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (28257)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28280)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28280)Refutation not found, incomplete strategy% (28280)------------------------------
% 0.21/0.54  % (28280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28280)Memory used [KB]: 6524
% 0.21/0.54  % (28280)Time elapsed: 0.120 s
% 0.21/0.54  % (28280)------------------------------
% 0.21/0.54  % (28280)------------------------------
% 0.21/0.54  % (28270)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (28277)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (28256)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28284)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28262)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (28265)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (28258)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (28255)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (28255)Refutation not found, incomplete strategy% (28255)------------------------------
% 0.21/0.55  % (28255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28255)Memory used [KB]: 1663
% 0.21/0.55  % (28255)Time elapsed: 0.128 s
% 0.21/0.55  % (28255)------------------------------
% 0.21/0.55  % (28255)------------------------------
% 0.21/0.55  % (28281)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (28273)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28267)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28265)Refutation not found, incomplete strategy% (28265)------------------------------
% 0.21/0.55  % (28265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28276)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (28264)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (28276)Refutation not found, incomplete strategy% (28276)------------------------------
% 0.21/0.55  % (28276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28276)Memory used [KB]: 1791
% 0.21/0.55  % (28276)Time elapsed: 0.140 s
% 0.21/0.55  % (28276)------------------------------
% 0.21/0.55  % (28276)------------------------------
% 0.21/0.55  % (28264)Refutation not found, incomplete strategy% (28264)------------------------------
% 0.21/0.55  % (28264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28265)Memory used [KB]: 10618
% 0.21/0.55  % (28265)Time elapsed: 0.098 s
% 0.21/0.55  % (28265)------------------------------
% 0.21/0.55  % (28265)------------------------------
% 0.21/0.55  % (28281)Refutation not found, incomplete strategy% (28281)------------------------------
% 0.21/0.55  % (28281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28281)Memory used [KB]: 10874
% 0.21/0.55  % (28281)Time elapsed: 0.111 s
% 0.21/0.55  % (28281)------------------------------
% 0.21/0.55  % (28281)------------------------------
% 0.21/0.55  % (28274)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (28272)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (28264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28264)Memory used [KB]: 10618
% 0.21/0.55  % (28264)Time elapsed: 0.123 s
% 0.21/0.55  % (28264)------------------------------
% 0.21/0.55  % (28264)------------------------------
% 0.21/0.55  % (28275)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (28278)Refutation not found, incomplete strategy% (28278)------------------------------
% 0.21/0.55  % (28278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28278)Memory used [KB]: 1791
% 0.21/0.55  % (28278)Time elapsed: 0.118 s
% 0.21/0.55  % (28278)------------------------------
% 0.21/0.55  % (28278)------------------------------
% 0.21/0.55  % (28257)Refutation not found, incomplete strategy% (28257)------------------------------
% 0.21/0.55  % (28257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28257)Memory used [KB]: 10746
% 0.21/0.55  % (28257)Time elapsed: 0.114 s
% 0.21/0.55  % (28257)------------------------------
% 0.21/0.55  % (28257)------------------------------
% 0.21/0.55  % (28270)Refutation not found, incomplete strategy% (28270)------------------------------
% 0.21/0.55  % (28270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28270)Memory used [KB]: 6140
% 0.21/0.55  % (28270)Time elapsed: 0.002 s
% 0.21/0.55  % (28270)------------------------------
% 0.21/0.55  % (28270)------------------------------
% 0.21/0.56  % (28269)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (28260)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (28262)Refutation not found, incomplete strategy% (28262)------------------------------
% 0.21/0.56  % (28262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28262)Memory used [KB]: 6396
% 0.21/0.56  % (28262)Time elapsed: 0.120 s
% 0.21/0.56  % (28262)------------------------------
% 0.21/0.56  % (28262)------------------------------
% 0.21/0.56  % (28283)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (28266)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.56  % (28271)# SZS output start Saturation.
% 0.21/0.56  tff(u1117,negated_conjecture,
% 0.21/0.56      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1116,negated_conjecture,
% 0.21/0.56      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1115,negated_conjecture,
% 0.21/0.56      ((~(sK1 != k7_subset_1(sK1,sK1,k1_xboole_0))) | (sK1 != k7_subset_1(sK1,sK1,k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1114,negated_conjecture,
% 0.21/0.56      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1113,negated_conjecture,
% 0.21/0.56      ((~(k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k1_xboole_0 != k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1112,axiom,
% 0.21/0.56      (![X0] : ((k5_xboole_0(X0,X0) = k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1111,axiom,
% 0.21/0.56      (![X3, X4] : ((k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1110,axiom,
% 0.21/0.56      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1109,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X0] : ((k1_xboole_0 = k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1108,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X1] : ((k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1107,negated_conjecture,
% 0.21/0.56      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1106,negated_conjecture,
% 0.21/0.56      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1105,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1104,axiom,
% 0.21/0.56      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1103,axiom,
% 0.21/0.56      ((~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1102,axiom,
% 0.21/0.56      (![X0] : ((k3_tarski(k1_zfmisc_1(X0)) = X0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1101,axiom,
% 0.21/0.56      (![X0] : ((k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1100,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X1] : ((k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1099,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1098,axiom,
% 0.21/0.56      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1097,axiom,
% 0.21/0.56      (![X1] : ((k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X1)) = k4_subset_1(X1,X1,X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1096,axiom,
% 0.21/0.56      (![X1, X3, X2] : ((k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)) = k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1095,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~(k1_xboole_0 = k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))) | (![X0] : ((k4_subset_1(X0,X0,k1_xboole_0) = X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1094,axiom,
% 0.21/0.56      (![X1] : ((k4_subset_1(X1,k1_xboole_0,X1) = X1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1093,axiom,
% 0.21/0.56      (![X2] : ((k4_subset_1(X2,X2,X2) = k3_subset_1(X2,k7_subset_1(k1_xboole_0,k1_xboole_0,X2)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1092,axiom,
% 0.21/0.56      (![X7, X6] : ((k4_subset_1(X6,X6,X6) = k3_subset_1(X6,k7_subset_1(X7,k1_xboole_0,X6)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1091,axiom,
% 0.21/0.56      (![X0] : ((k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1090,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1089,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)))) | (![X0] : ((k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1088,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1087,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1086,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1085,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1084,negated_conjecture,
% 0.21/0.56      ((~(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1083,axiom,
% 0.21/0.56      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1082,axiom,
% 0.21/0.56      (![X3, X2] : ((k7_subset_1(X2,k1_xboole_0,X3) = k7_subset_1(k1_xboole_0,k1_xboole_0,X3))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1081,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1080,negated_conjecture,
% 0.21/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X4] : ((k7_subset_1(u1_struct_0(sK0),sK1,X4) = k7_subset_1(sK1,sK1,X4)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1079,axiom,
% 0.21/0.56      (![X0] : ((k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1078,negated_conjecture,
% 0.21/0.56      ((~(u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1))) | (u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1077,negated_conjecture,
% 0.21/0.56      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1076,negated_conjecture,
% 0.21/0.56      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1075,negated_conjecture,
% 0.21/0.56      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1074,negated_conjecture,
% 0.21/0.56      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1073,negated_conjecture,
% 0.21/0.56      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1))) | (sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1072,negated_conjecture,
% 0.21/0.56      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1071,axiom,
% 0.21/0.56      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1070,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1069,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1068,axiom,
% 0.21/0.56      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k3_subset_1(X1,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X1,X1,X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1067,axiom,
% 0.21/0.56      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k3_subset_1(X4,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,k1_xboole_0,X3)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1066,axiom,
% 0.21/0.56      (![X3, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(X4)) | (k4_subset_1(X4,X4,X3) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1065,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1064,axiom,
% 0.21/0.56      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | (k4_subset_1(X1,k1_xboole_0,X0) = X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1063,axiom,
% 0.21/0.56      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1062,negated_conjecture,
% 0.21/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X2) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X2)))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1061,negated_conjecture,
% 0.21/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X2) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X2)))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1060,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1059,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1))) | ~m1_subset_1(k7_subset_1(sK1,sK1,k1_xboole_0),k1_zfmisc_1(sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1058,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1057,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : (~m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1056,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1055,axiom,
% 0.21/0.56      ((~(k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (![X0] : ((~m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) | ~r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) | (k7_subset_1(X0,X0,k1_xboole_0) = X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1054,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1053,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))))).
% 0.21/0.56  
% 0.21/0.56  % (28266)Refutation not found, incomplete strategy% (28266)------------------------------
% 0.21/0.56  % (28266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  tff(u1052,negated_conjecture,
% 0.21/0.56      ((~~m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1051,axiom,
% 0.21/0.56      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.56  
% 0.21/0.56  % (28266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  tff(u1050,axiom,
% 0.21/0.56      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1049,negated_conjecture,
% 0.21/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.56  
% 0.21/0.56  % (28266)Memory used [KB]: 10618
% 0.21/0.56  % (28266)Time elapsed: 0.150 s
% 0.21/0.56  % (28266)------------------------------
% 0.21/0.56  % (28266)------------------------------
% 0.21/0.56  tff(u1048,axiom,
% 0.21/0.56      (![X1, X0] : ((~r1_tarski(X1,k3_subset_1(X0,X1)) | (k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1047,axiom,
% 0.21/0.56      (![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1046,axiom,
% 0.21/0.56      (![X1, X0] : ((~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | (X0 = X1))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1045,negated_conjecture,
% 0.21/0.56      ((~~r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))) | ~r1_tarski(k3_subset_1(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1044,negated_conjecture,
% 0.21/0.56      ((~~r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)))) | ~r1_tarski(k3_subset_1(k1_xboole_0,k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1043,axiom,
% 0.21/0.56      (![X1, X0] : ((~r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(X0,k1_xboole_0,X0) = X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1042,axiom,
% 0.21/0.56      (![X9, X8, X10] : ((~r1_tarski(k3_subset_1(X8,k7_subset_1(X10,k1_xboole_0,X8)),k7_subset_1(X9,k1_xboole_0,X8)) | ~m1_subset_1(k7_subset_1(X9,k1_xboole_0,X8),k1_zfmisc_1(X8)) | (k7_subset_1(X9,k1_xboole_0,X8) = X8))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1041,axiom,
% 0.21/0.56      (![X0] : ((~r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(X0,k1_xboole_0,X0) = X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1040,axiom,
% 0.21/0.56      (![X0] : ((~r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) | (k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1039,axiom,
% 0.21/0.56      (![X3, X2] : ((~r1_tarski(k4_subset_1(X2,X2,X2),k7_subset_1(X3,k1_xboole_0,X2)) | ~m1_subset_1(k7_subset_1(X3,k1_xboole_0,X2),k1_zfmisc_1(X2)) | (k7_subset_1(X3,k1_xboole_0,X2) = X2))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1038,negated_conjecture,
% 0.21/0.56      ((~~r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0)) | ~r1_tarski(k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0)),k1_xboole_0))).
% 0.21/0.56  
% 0.21/0.56  tff(u1037,axiom,
% 0.21/0.56      (![X1] : ((~r1_tarski(k7_subset_1(X1,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) | (k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X1)) | ~m1_subset_1(k7_subset_1(X1,k1_xboole_0,X1),k1_zfmisc_1(X1)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1036,axiom,
% 0.21/0.56      (![X1] : ((~r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) | (k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) | ~m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(X1)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1035,axiom,
% 0.21/0.56      (![X5, X4] : ((~r1_tarski(k7_subset_1(X5,k1_xboole_0,X4),k4_subset_1(X4,X4,X4)) | (k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X4)) | ~m1_subset_1(k7_subset_1(X5,k1_xboole_0,X4),k1_zfmisc_1(X4)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1034,axiom,
% 0.21/0.56      (![X1, X0] : ((~r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0))) | (k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0)) | ~m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1033,axiom,
% 0.21/0.56      (![X11, X13, X12] : ((~r1_tarski(k7_subset_1(X12,k1_xboole_0,X11),k3_subset_1(X11,k7_subset_1(X13,k1_xboole_0,X11))) | (k1_xboole_0 = k7_subset_1(X12,k1_xboole_0,X11)) | ~m1_subset_1(k7_subset_1(X12,k1_xboole_0,X11),k1_zfmisc_1(X11)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1032,axiom,
% 0.21/0.56      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u1031,negated_conjecture,
% 0.21/0.56      ((~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1)) | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),sK1))).
% 0.21/0.56  
% 0.21/0.56  tff(u1030,axiom,
% 0.21/0.56      (![X1] : ((~l1_struct_0(X1) | (u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1029,axiom,
% 0.21/0.56      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u1028,negated_conjecture,
% 0.21/0.56      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  % (28272)Refutation not found, incomplete strategy% (28272)------------------------------
% 0.21/0.56  % (28272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28271)# SZS output end Saturation.
% 0.21/0.56  % (28272)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28271)------------------------------
% 0.21/0.56  % (28271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28272)Memory used [KB]: 10618
% 0.21/0.56  % (28271)Termination reason: Satisfiable
% 0.21/0.56  
% 0.21/0.56  % (28272)Time elapsed: 0.147 s
% 0.21/0.56  % (28272)------------------------------
% 0.21/0.56  % (28272)------------------------------
% 0.21/0.56  % (28271)Memory used [KB]: 11385
% 0.21/0.56  % (28271)Time elapsed: 0.132 s
% 0.21/0.56  % (28271)------------------------------
% 0.21/0.56  % (28271)------------------------------
% 0.21/0.56  % (28254)Success in time 0.181 s
%------------------------------------------------------------------------------
