%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:02 EST 2020

% Result     : CounterSatisfiable 8.11s
% Output     : Saturation 8.11s
% Verified   : 
% Statistics : Number of formulae       :  307 ( 307 expanded)
%              Number of leaves         :  307 ( 307 expanded)
%              Depth                    :    0
%              Number of atoms          :  635 ( 635 expanded)
%              Number of equality atoms :  577 ( 577 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u28642,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u28641,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u28640,axiom,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 )).

tff(u28639,axiom,(
    ! [X13,X14] :
      ( k4_xboole_0(X13,k1_tarski(X14)) = X13
      | k1_tarski(X14) = k3_xboole_0(k1_tarski(X14),X13) ) )).

tff(u28638,axiom,(
    ! [X18,X17] :
      ( k4_xboole_0(X18,k1_tarski(X17)) = X18
      | k1_tarski(X17) = k3_xboole_0(X18,k1_tarski(X17)) ) )).

tff(u28637,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u28636,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u28635,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u28634,axiom,(
    ! [X11,X10] : k4_xboole_0(X10,X11) = k3_xboole_0(k4_xboole_0(X10,X11),X10) )).

tff(u28633,axiom,(
    ! [X5,X4] : k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5) )).

tff(u28632,axiom,(
    ! [X1,X2] :
      ( k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X1),X2) ) )).

tff(u28631,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u28630,axiom,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) )).

tff(u28629,axiom,(
    ! [X29,X30] : k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X30,X29),k3_xboole_0(X29,X30)) )).

tff(u28628,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X8,X7)) )).

tff(u28627,axiom,(
    ! [X15,X14] : k3_xboole_0(X15,X14) = k3_xboole_0(k3_xboole_0(X15,X14),k3_xboole_0(X14,X15)) )).

tff(u28626,axiom,(
    ! [X84,X83] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X83),k3_xboole_0(k1_tarski(X83),X84))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X83))
      | k1_tarski(X83) = k3_xboole_0(X84,k1_tarski(X83)) ) )).

tff(u28625,axiom,(
    ! [X40,X39] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X39),k3_xboole_0(k1_tarski(X39),X40))
      | k1_tarski(X39) = k3_xboole_0(X40,k1_tarski(X39))
      | k1_xboole_0 = k1_tarski(X39) ) )).

tff(u28624,axiom,(
    ! [X150,X151] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X150),k3_xboole_0(k1_tarski(X150),X151))
      | k1_tarski(X150) = k3_xboole_0(X151,k1_tarski(X150)) ) )).

tff(u28623,axiom,(
    ! [X16,X15] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X15),k3_xboole_0(k1_tarski(X15),X16))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X15),X16)) ) )).

tff(u28622,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X51),k3_xboole_0(k1_tarski(X51),X52))
      | k1_tarski(X51) = k3_xboole_0(k1_tarski(X51),X52) ) )).

tff(u28621,axiom,(
    ! [X5,X6] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),X6))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6) ) )).

tff(u28620,axiom,(
    ! [X34,X35] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X35),k3_xboole_0(k1_tarski(X34),k1_tarski(X35)))
      | k1_tarski(X34) = k3_xboole_0(k1_tarski(X35),k1_tarski(X34))
      | k1_xboole_0 = k1_tarski(X35) ) )).

tff(u28619,axiom,(
    ! [X29,X28] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X29),k3_xboole_0(k1_tarski(X28),k1_tarski(X29)))
      | k1_tarski(X28) = k3_xboole_0(k1_tarski(X28),k1_tarski(X29))
      | k1_xboole_0 = k1_tarski(X29) ) )).

tff(u28618,axiom,(
    ! [X25,X24] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X25),k3_xboole_0(k1_tarski(X24),k1_tarski(X25)))
      | k1_tarski(X25) = k1_tarski(X24)
      | k1_xboole_0 = k1_tarski(X25) ) )).

tff(u28617,axiom,(
    ! [X18,X17] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k3_xboole_0(k1_tarski(X17),k1_tarski(X18)))
      | k1_tarski(X18) = k3_xboole_0(k1_tarski(X18),k1_tarski(X17))
      | k1_xboole_0 = k1_tarski(X17) ) )).

tff(u28616,axiom,(
    ! [X25,X26] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X26),k3_xboole_0(k1_tarski(X26),k1_tarski(X25)))
      | k1_tarski(X25) = k3_xboole_0(k1_tarski(X26),k1_tarski(X25))
      | k1_xboole_0 = k1_tarski(X26) ) )).

tff(u28615,axiom,(
    ! [X13,X14] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X13),k3_xboole_0(k1_tarski(X13),k1_tarski(X14)))
      | k1_tarski(X13) = k1_tarski(X14)
      | k1_xboole_0 = k1_tarski(X13) ) )).

tff(u28614,axiom,(
    ! [X18,X17] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k3_xboole_0(X18,k1_tarski(X17)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X17),X18)) ) )).

tff(u28613,axiom,(
    ! [X55,X56] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X55),k3_xboole_0(X56,k1_tarski(X55)))
      | k1_tarski(X55) = k3_xboole_0(X56,k1_tarski(X55)) ) )).

tff(u28612,axiom,(
    ! [X53,X54] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X53),k3_xboole_0(X54,k1_tarski(X53)))
      | k1_tarski(X53) = k3_xboole_0(k1_tarski(X53),X54) ) )).

tff(u28611,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28610,axiom,(
    ! [X5,X6] :
      ( k1_tarski(X5) = k3_xboole_0(k1_tarski(X5),k3_xboole_0(X6,k1_tarski(X5)))
      | k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),X6) ) )).

tff(u28609,axiom,(
    ! [X46,X45] :
      ( k1_tarski(X45) = k3_xboole_0(k1_tarski(X45),k3_xboole_0(X46,k1_tarski(X45)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X45),X46) ) )).

tff(u28608,axiom,(
    ! [X16,X17] :
      ( k1_tarski(X17) = k3_xboole_0(k1_tarski(X17),k3_xboole_0(X16,k1_tarski(X17)))
      | k1_xboole_0 = k3_xboole_0(X16,k1_tarski(X17)) ) )).

tff(u28607,axiom,(
    ! [X29,X28] :
      ( k1_tarski(X29) = k3_xboole_0(k1_tarski(X29),k3_xboole_0(X28,k1_tarski(X29)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X28,k1_tarski(X29))) ) )).

tff(u28606,axiom,(
    ! [X29,X28] :
      ( k1_tarski(X28) = k3_xboole_0(k1_tarski(X28),k3_xboole_0(X29,k1_tarski(X28)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X28),X29))
      | k1_xboole_0 = k1_tarski(X28) ) )).

tff(u28605,axiom,(
    ! [X95,X94] :
      ( k1_tarski(X94) = k3_xboole_0(k1_tarski(X94),k3_xboole_0(X95,k1_tarski(X94)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X94))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X94),X95)) ) )).

tff(u28604,axiom,(
    ! [X106,X105] :
      ( k1_tarski(X105) = k3_xboole_0(k1_tarski(X105),k3_xboole_0(X106,k1_tarski(X105)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X105),X106)) ) )).

tff(u28603,axiom,(
    ! [X11,X10] :
      ( k1_tarski(X10) = k3_xboole_0(k1_tarski(X10),k3_xboole_0(k1_tarski(X10),X11))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X11,k1_tarski(X10)))
      | k1_xboole_0 = k1_tarski(X10) ) )).

tff(u28602,axiom,(
    ! [X38,X37] :
      ( k1_tarski(X37) = k3_xboole_0(k1_tarski(X37),k3_xboole_0(k1_tarski(X37),X38))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X38,k1_tarski(X37))) ) )).

tff(u28601,axiom,(
    ! [X20,X19] :
      ( k1_tarski(X19) = k3_xboole_0(k1_tarski(X19),k3_xboole_0(k1_tarski(X19),X20))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X19),X20)) ) )).

tff(u28600,axiom,(
    ! [X3,X4] :
      ( k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),X4))
      | k1_tarski(X3) = k4_xboole_0(k1_tarski(X3),X4) ) )).

tff(u28599,axiom,(
    ! [X48,X47] :
      ( k1_tarski(X48) = k3_xboole_0(k1_tarski(X48),k3_xboole_0(k1_tarski(X48),X47))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X48),X47) ) )).

tff(u28598,axiom,(
    ! [X46,X45] :
      ( k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),k3_xboole_0(k1_tarski(X46),X45))
      | k1_xboole_0 = k3_xboole_0(X45,k1_tarski(X46)) ) )).

tff(u28597,axiom,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

tff(u28596,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) )).

tff(u28595,axiom,(
    ! [X20,X21] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X20),X21)) ) )).

tff(u28594,axiom,(
    ! [X58,X59] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X58),k4_xboole_0(k1_tarski(X58),X59))
      | k1_tarski(X58) = k4_xboole_0(k1_tarski(X58),X59) ) )).

tff(u28593,axiom,(
    ! [X18,X17] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k4_xboole_0(k1_tarski(X17),X18))
      | k1_xboole_0 = k3_xboole_0(X18,k1_tarski(X17)) ) )).

tff(u28592,axiom,(
    ! [X11,X10] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X10),X11) ) )).

tff(u28591,axiom,(
    ! [X16,X17] :
      ( k1_tarski(X16) = k3_xboole_0(k1_tarski(X16),k4_xboole_0(k1_tarski(X16),X17))
      | k1_tarski(X16) = k3_xboole_0(X17,k1_tarski(X16))
      | k1_xboole_0 = k1_tarski(X16) ) )).

tff(u28590,axiom,(
    ! [X22,X23] :
      ( k1_tarski(X22) = k3_xboole_0(k1_tarski(X22),k4_xboole_0(k1_tarski(X22),X23))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X22),X23)) ) )).

tff(u28589,axiom,(
    ! [X71,X70] :
      ( k1_tarski(X70) = k3_xboole_0(k1_tarski(X70),k4_xboole_0(k1_tarski(X70),X71))
      | k1_tarski(X70) = k3_xboole_0(X71,k1_tarski(X70)) ) )).

tff(u28588,axiom,(
    ! [X9,X8] :
      ( k1_tarski(X8) = k3_xboole_0(k1_tarski(X8),k4_xboole_0(k1_tarski(X8),X9))
      | k1_tarski(X8) = k3_xboole_0(k1_tarski(X8),X9) ) )).

tff(u28587,axiom,(
    ! [X11,X10] :
      ( k1_tarski(X10) = k3_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X10),X11) ) )).

tff(u28586,axiom,(
    ! [X3,X4] :
      ( k1_tarski(X3) = k3_xboole_0(X4,k1_tarski(X3))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4) ) )).

tff(u28585,axiom,(
    ! [X3,X4] :
      ( k1_tarski(X3) = k3_xboole_0(X4,k1_tarski(X3))
      | k1_xboole_0 = k3_xboole_0(X4,k1_tarski(X3)) ) )).

tff(u28584,axiom,(
    ! [X42,X41] :
      ( k1_tarski(X41) = k3_xboole_0(k3_xboole_0(X42,k1_tarski(X41)),k1_tarski(X41))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X41),X42) ) )).

tff(u28583,axiom,(
    ! [X13,X14] :
      ( k1_tarski(X13) = k3_xboole_0(k3_xboole_0(X14,k1_tarski(X13)),k1_tarski(X13))
      | k1_xboole_0 = k3_xboole_0(X14,k1_tarski(X13)) ) )).

tff(u28582,axiom,(
    ! [X16,X15] :
      ( k1_tarski(X15) = k3_xboole_0(k3_xboole_0(X16,k1_tarski(X15)),k1_tarski(X15))
      | k1_tarski(X15) = k4_xboole_0(k1_tarski(X15),X16) ) )).

tff(u28581,axiom,(
    ! [X20,X21] :
      ( k1_tarski(X20) = k3_xboole_0(k3_xboole_0(X21,k1_tarski(X20)),k1_tarski(X20))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X20),X21))
      | k1_xboole_0 = k1_tarski(X20) ) )).

tff(u28580,axiom,(
    ! [X98,X99] :
      ( k1_tarski(X98) = k3_xboole_0(k3_xboole_0(X99,k1_tarski(X98)),k1_tarski(X98))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X98))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X98),X99)) ) )).

tff(u28579,axiom,(
    ! [X22,X23] :
      ( k1_tarski(X22) = k3_xboole_0(k3_xboole_0(X23,k1_tarski(X22)),k1_tarski(X22))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X23,k1_tarski(X22)))
      | k1_xboole_0 = k1_tarski(X22) ) )).

tff(u28578,axiom,(
    ! [X100,X101] :
      ( k1_tarski(X100) = k3_xboole_0(k3_xboole_0(X101,k1_tarski(X100)),k1_tarski(X100))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X100))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X101,k1_tarski(X100))) ) )).

tff(u28577,axiom,(
    ! [X141,X140] :
      ( k1_tarski(X140) = k3_xboole_0(k3_xboole_0(X141,k1_tarski(X140)),k1_tarski(X140))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X141,k1_tarski(X140))) ) )).

tff(u28576,axiom,(
    ! [X145,X144] :
      ( k1_tarski(X144) = k3_xboole_0(k3_xboole_0(X145,k1_tarski(X144)),k1_tarski(X144))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X144),X145)) ) )).

tff(u28575,axiom,(
    ! [X42,X41] :
      ( k1_tarski(X42) = k3_xboole_0(k3_xboole_0(k1_tarski(X42),X41),k1_tarski(X42))
      | k1_xboole_0 = k3_xboole_0(X41,k1_tarski(X42)) ) )).

tff(u28574,axiom,(
    ! [X9,X10] :
      ( k1_tarski(X9) = k3_xboole_0(k3_xboole_0(k1_tarski(X9),X10),k1_tarski(X9))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X9),X10) ) )).

tff(u28573,axiom,(
    ! [X13,X14] :
      ( k1_tarski(X13) = k3_xboole_0(k3_xboole_0(k1_tarski(X13),X14),k1_tarski(X13))
      | k1_tarski(X13) = k4_xboole_0(k1_tarski(X13),X14) ) )).

tff(u28572,axiom,(
    ! [X18,X19] :
      ( k1_tarski(X18) = k3_xboole_0(k3_xboole_0(k1_tarski(X18),X19),k1_tarski(X18))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X18),X19))
      | k1_xboole_0 = k1_tarski(X18) ) )).

tff(u28571,axiom,(
    ! [X96,X97] :
      ( k1_tarski(X96) = k3_xboole_0(k3_xboole_0(k1_tarski(X96),X97),k1_tarski(X96))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X96))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X96),X97)) ) )).

tff(u28570,axiom,(
    ! [X129,X130] :
      ( k1_tarski(X129) = k3_xboole_0(k3_xboole_0(k1_tarski(X129),X130),k1_tarski(X129))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X129),X130)) ) )).

tff(u28569,axiom,(
    ! [X16,X17] :
      ( k1_tarski(X17) = k3_xboole_0(k3_xboole_0(k1_tarski(X17),X16),k1_tarski(X17))
      | k1_xboole_0 = k1_tarski(X17)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X16,k1_tarski(X17))) ) )).

tff(u28568,axiom,(
    ! [X143,X142] :
      ( k1_tarski(X143) = k3_xboole_0(k3_xboole_0(k1_tarski(X143),X142),k1_tarski(X143))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X143))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X142,k1_tarski(X143))) ) )).

tff(u28567,axiom,(
    ! [X195,X194] :
      ( k1_tarski(X195) = k3_xboole_0(k3_xboole_0(k1_tarski(X195),X194),k1_tarski(X195))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X194,k1_tarski(X195))) ) )).

tff(u28566,axiom,(
    ! [X16,X17] :
      ( k1_tarski(X16) = k3_xboole_0(k4_xboole_0(k1_tarski(X16),X17),k1_tarski(X16))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X16),X17) ) )).

tff(u28565,axiom,(
    ! [X18,X19] :
      ( k1_tarski(X18) = k3_xboole_0(k4_xboole_0(k1_tarski(X18),X19),k1_tarski(X18))
      | k1_tarski(X18) = k3_xboole_0(k1_tarski(X18),X19) ) )).

tff(u28564,axiom,(
    ! [X27,X26] :
      ( k1_tarski(X26) = k3_xboole_0(k4_xboole_0(k1_tarski(X26),X27),k1_tarski(X26))
      | k1_xboole_0 = k1_tarski(X26)
      | k1_tarski(X26) = k3_xboole_0(X27,k1_tarski(X26)) ) )).

tff(u28563,axiom,(
    ! [X29,X28] :
      ( k1_tarski(X28) = k3_xboole_0(k4_xboole_0(k1_tarski(X28),X29),k1_tarski(X28))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X28))
      | k1_tarski(X28) = k3_xboole_0(X29,k1_tarski(X28)) ) )).

tff(u28562,axiom,(
    ! [X49,X50] :
      ( k1_tarski(X49) = k3_xboole_0(k4_xboole_0(k1_tarski(X49),X50),k1_tarski(X49))
      | k1_tarski(X49) = k3_xboole_0(X50,k1_tarski(X49)) ) )).

tff(u28561,axiom,(
    ! [X15,X14] :
      ( k1_tarski(X14) = k3_xboole_0(k4_xboole_0(k1_tarski(X14),X15),k1_tarski(X14))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X14),X15))
      | k1_xboole_0 = k1_tarski(X14) ) )).

tff(u28560,axiom,(
    ! [X93,X92] :
      ( k1_tarski(X92) = k3_xboole_0(k4_xboole_0(k1_tarski(X92),X93),k1_tarski(X92))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X92))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X92),X93)) ) )).

tff(u28559,axiom,(
    ! [X131,X130] :
      ( k1_tarski(X130) = k3_xboole_0(k4_xboole_0(k1_tarski(X130),X131),k1_tarski(X130))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X130),X131)) ) )).

tff(u28558,axiom,(
    ! [X3,X4] :
      ( k1_tarski(X4) = k3_xboole_0(k1_tarski(X4),X3)
      | k1_xboole_0 = k3_xboole_0(X3,k1_tarski(X4)) ) )).

tff(u28557,axiom,(
    ! [X18,X19] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X19),k1_tarski(X18))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X18),k1_tarski(X19))
      | k1_tarski(X18) = k1_tarski(X19) ) )).

tff(u28556,axiom,(
    ! [X58,X59] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X58),k1_tarski(X59))
      | k1_xboole_0 = k1_tarski(X59)
      | k1_tarski(X58) = k1_tarski(X59) ) )).

tff(u28555,axiom,(
    ! [X15,X14] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X14),k1_tarski(X15))
      | k1_xboole_0 = k1_tarski(X14)
      | k1_tarski(X15) = k1_tarski(X14) ) )).

tff(u28554,axiom,(
    ! [X22,X23] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X23),k1_tarski(X22))
      | k1_tarski(X23) = k1_tarski(X22) ) )).

tff(u28553,axiom,(
    ! [X25,X26] :
      ( k1_tarski(X25) = k3_xboole_0(k3_xboole_0(k1_tarski(X25),X26),k1_tarski(X25))
      | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X26,k1_tarski(X25)),k1_tarski(X25)) ) )).

tff(u28552,axiom,(
    ! [X23,X24] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X24,k1_tarski(X23)),k1_tarski(X23))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X23),X24)) ) )).

tff(u28551,axiom,(
    ! [X13,X14] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,k1_tarski(X13)),k1_tarski(X13))
      | k1_tarski(X13) = k3_xboole_0(k1_tarski(X13),X14) ) )).

tff(u28550,axiom,(
    ! [X53,X54] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X53,k1_tarski(X54)),k1_tarski(X54))
      | k1_tarski(X54) = k3_xboole_0(X53,k1_tarski(X54)) ) )).

tff(u28549,axiom,(
    ! [X9,X10] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X10,k1_tarski(X9)),k1_tarski(X9))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X9),X10) ) )).

tff(u28548,axiom,(
    ! [X73,X72] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X73),k1_tarski(X72)),k1_tarski(X72))
      | k1_xboole_0 = k1_tarski(X72)
      | k1_xboole_0 = k1_tarski(X73)
      | k1_tarski(X72) = k1_tarski(X73) ) )).

tff(u28547,axiom,(
    ! [X38,X37] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X38),k1_tarski(X37)),k1_tarski(X37))
      | k1_tarski(X38) = k3_xboole_0(k1_tarski(X37),k1_tarski(X38))
      | k1_xboole_0 = k1_tarski(X37) ) )).

tff(u28546,axiom,(
    ! [X79,X78] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X79),k1_tarski(X78)),k1_tarski(X78))
      | k1_xboole_0 = k1_tarski(X78)
      | k1_tarski(X79) = k3_xboole_0(k1_tarski(X79),k1_tarski(X78)) ) )).

tff(u28545,axiom,(
    ! [X75,X74] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X75),k1_tarski(X74)),k1_tarski(X74))
      | k1_xboole_0 = k1_tarski(X74)
      | k1_tarski(X74) = k1_tarski(X75) ) )).

tff(u28544,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X51),X52),k1_tarski(X51))
      | k1_tarski(X51) = k3_xboole_0(k1_tarski(X51),X52) ) )).

tff(u28543,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28542,axiom,(
    ! [X22,X21] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X21),X22),k1_tarski(X21))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X21),X22)) ) )).

tff(u28541,axiom,(
    ! [X38,X37] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X37),X38),k1_tarski(X37))
      | k1_tarski(X37) = k3_xboole_0(X38,k1_tarski(X37))
      | k1_xboole_0 = k1_tarski(X37) ) )).

tff(u28540,axiom,(
    ! [X102,X101] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X101),X102),k1_tarski(X101))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X101))
      | k1_tarski(X101) = k3_xboole_0(X102,k1_tarski(X101)) ) )).

tff(u28539,axiom,(
    ! [X172,X171] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X171),X172),k1_tarski(X171))
      | k1_tarski(X171) = k3_xboole_0(X172,k1_tarski(X171)) ) )).

tff(u28538,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X49),X50),k1_tarski(X49))
      | k1_tarski(X49) = k3_xboole_0(k3_xboole_0(X50,k1_tarski(X49)),k1_tarski(X49)) ) )).

tff(u28537,axiom,(
    ! [X25,X24] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X25),k1_tarski(X24)),k1_tarski(X25))
      | k1_tarski(X24) = k3_xboole_0(k1_tarski(X24),k1_tarski(X25))
      | k1_xboole_0 = k1_tarski(X25) ) )).

tff(u28536,axiom,(
    ! [X95,X94] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X95),k1_tarski(X94)),k1_tarski(X95))
      | k1_xboole_0 = k1_tarski(X95)
      | k1_tarski(X94) = k3_xboole_0(k1_tarski(X95),k1_tarski(X94)) ) )).

tff(u28535,axiom,(
    ! [X23,X24] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X24),k1_tarski(X23)),k1_tarski(X24))
      | k1_xboole_0 = k1_tarski(X24)
      | k1_tarski(X23) = k1_tarski(X24) ) )).

tff(u28534,axiom,(
    ! [X27,X26] :
      ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X26),X27),k1_tarski(X26))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X26),X27)) ) )).

tff(u28533,axiom,(
    ! [X56,X57] :
      ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X56),X57),k1_tarski(X56))
      | k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),X57) ) )).

tff(u28532,axiom,(
    ! [X22,X21] :
      ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X21),X22),k1_tarski(X21))
      | k1_xboole_0 = k3_xboole_0(X22,k1_tarski(X21)) ) )).

tff(u28531,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_tarski(X12))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28530,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

tff(u28529,axiom,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) )).

tff(u28528,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u28527,axiom,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) )).

tff(u28526,axiom,(
    ! [X15,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14) )).

tff(u28525,axiom,(
    ! [X5,X4] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X4),X4) )).

tff(u28524,axiom,(
    ! [X16,X15] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X16),X15)
      | k1_xboole_0 = k3_xboole_0(X15,k1_tarski(X16)) ) )).

tff(u28523,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28522,axiom,(
    ! [X23,X24] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X23)) )).

tff(u28521,axiom,(
    ! [X18,X17] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X17),k3_xboole_0(X18,k1_tarski(X17)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X18,k1_tarski(X17))) ) )).

tff(u28520,axiom,(
    ! [X16,X15] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X15),k3_xboole_0(X16,k1_tarski(X15)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X15),X16)) ) )).

tff(u28519,axiom,(
    ! [X22,X21] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X21),k3_xboole_0(X22,k1_tarski(X21)))
      | k1_tarski(X21) = k4_xboole_0(k1_tarski(X21),X22) ) )).

tff(u28518,axiom,(
    ! [X42,X41] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X41),k3_xboole_0(X42,k1_tarski(X41)))
      | k1_xboole_0 = k3_xboole_0(X42,k1_tarski(X41)) ) )).

tff(u28517,axiom,(
    ! [X38,X37] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X37),k3_xboole_0(X38,k1_tarski(X37)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X37),X38) ) )).

tff(u28516,axiom,(
    ! [X38,X37] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X38),k3_xboole_0(k1_tarski(X38),X37))
      | k1_xboole_0 = k3_xboole_0(X37,k1_tarski(X38)) ) )).

tff(u28515,axiom,(
    ! [X20,X19] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X19),k3_xboole_0(k1_tarski(X19),X20))
      | k1_tarski(X19) = k4_xboole_0(k1_tarski(X19),X20) ) )).

tff(u28514,axiom,(
    ! [X40,X39] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X40),k3_xboole_0(k1_tarski(X40),X39))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X40),X39) ) )).

tff(u28513,axiom,(
    ! [X13,X14] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X13),k3_xboole_0(k1_tarski(X13),X14))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X13),X14)) ) )).

tff(u28512,axiom,(
    ! [X91,X92] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X91),k3_xboole_0(k1_tarski(X91),X92))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X91))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X92,k1_tarski(X91))) ) )).

tff(u28511,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X51),k3_xboole_0(k1_tarski(X51),X52))
      | k1_xboole_0 = k1_tarski(X51)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X52,k1_tarski(X51))) ) )).

tff(u28510,axiom,(
    ! [X164,X163] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X163),k3_xboole_0(k1_tarski(X163),X164))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X164,k1_tarski(X163))) ) )).

tff(u28509,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X50),k1_tarski(X49)),k1_xboole_0)
      | k1_tarski(X49) = k1_tarski(X50) ) )).

tff(u28508,axiom,(
    ! [X178,X177] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X177),X178),k1_xboole_0)
      | k1_tarski(X177) = k3_xboole_0(X178,k1_tarski(X177)) ) )).

tff(u28507,axiom,(
    ! [X42,X41] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X42),X41),k1_xboole_0)
      | k1_tarski(X42) = k3_xboole_0(k1_tarski(X42),X41) ) )).

tff(u28506,axiom,(
    ! [X51,X50] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X50),X51),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X50),X51) ) )).

tff(u28505,axiom,(
    ! [X89,X90] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X90,k1_tarski(X89)),k1_xboole_0)
      | k1_tarski(X89) = k3_xboole_0(k1_tarski(X89),X90) ) )).

tff(u28504,axiom,(
    ! [X38,X37] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X38,k1_tarski(X37)),k1_xboole_0)
      | k1_tarski(X37) = k3_xboole_0(X38,k1_tarski(X37)) ) )).

tff(u28503,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28502,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0)
      | k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28501,axiom,(
    ! [X81,X80] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X80),X81),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(X81,k1_tarski(X80)) ) )).

tff(u28500,axiom,(
    ! [X58,X59] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X58),X59),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X58),X59) ) )).

tff(u28499,axiom,(
    ! [X20,X21] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X20),X21)) ) )).

tff(u28498,axiom,(
    ! [X32,X31] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X31),k4_xboole_0(k1_tarski(X31),X32))
      | k1_tarski(X31) = k3_xboole_0(X32,k1_tarski(X31)) ) )).

tff(u28497,axiom,(
    ! [X25,X24] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X24),k4_xboole_0(k1_tarski(X24),X25))
      | k1_tarski(X24) = k3_xboole_0(k1_tarski(X24),X25) ) )).

tff(u28496,axiom,(
    ! [X20,X21] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X20),X21) ) )).

tff(u28495,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u28494,axiom,(
    ! [X5,X4] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) )).

tff(u28493,axiom,(
    ! [X9,X10] :
      ( k1_tarski(X9) = k4_xboole_0(k1_tarski(X9),X10)
      | k1_tarski(X9) = k3_xboole_0(X10,k1_tarski(X9)) ) )).

tff(u28492,axiom,(
    ! [X15,X14] :
      ( k1_tarski(X14) = k4_xboole_0(k1_tarski(X14),X15)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X14),X15) ) )).

tff(u28491,axiom,(
    ! [X1,X2] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)
      | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2) ) )).

tff(u28490,axiom,(
    ! [X22,X23] :
      ( k1_tarski(X22) = k4_xboole_0(k1_tarski(X22),k3_xboole_0(k1_tarski(X22),X23))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X22),X23) ) )).

tff(u28489,axiom,(
    ! [X56,X57] :
      ( k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),k3_xboole_0(k1_tarski(X56),X57))
      | k1_tarski(X56) = k3_xboole_0(k1_tarski(X56),X57) ) )).

tff(u28488,axiom,(
    ! [X32,X31] :
      ( k1_tarski(X31) = k4_xboole_0(k1_tarski(X31),k3_xboole_0(k1_tarski(X31),X32))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X31),k3_xboole_0(X32,k1_tarski(X31))) ) )).

tff(u28487,axiom,(
    ! [X84,X85] :
      ( k1_tarski(X84) = k4_xboole_0(k1_tarski(X84),k3_xboole_0(k1_tarski(X84),X85))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X84))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X84),X85)) ) )).

tff(u28486,axiom,(
    ! [X16,X17] :
      ( k1_tarski(X16) = k4_xboole_0(k1_tarski(X16),k3_xboole_0(k1_tarski(X16),X17))
      | k1_xboole_0 = k1_tarski(X16)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X16),X17)) ) )).

tff(u28485,axiom,(
    ! [X98,X99] :
      ( k1_tarski(X98) = k4_xboole_0(k1_tarski(X98),k3_xboole_0(k1_tarski(X98),X99))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X98),X99)) ) )).

tff(u28484,axiom,(
    ! [X15,X14] :
      ( k1_tarski(X14) = k4_xboole_0(k1_tarski(X14),k3_xboole_0(k1_tarski(X14),X15))
      | k1_xboole_0 = k1_tarski(X14)
      | k1_tarski(X14) = k3_xboole_0(X15,k1_tarski(X14)) ) )).

tff(u28483,axiom,(
    ! [X115,X116] :
      ( k1_tarski(X115) = k4_xboole_0(k1_tarski(X115),k3_xboole_0(k1_tarski(X115),X116))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X115))
      | k1_tarski(X115) = k3_xboole_0(X116,k1_tarski(X115)) ) )).

tff(u28482,axiom,(
    ! [X148,X149] :
      ( k1_tarski(X148) = k4_xboole_0(k1_tarski(X148),k3_xboole_0(k1_tarski(X148),X149))
      | k1_tarski(X148) = k3_xboole_0(X149,k1_tarski(X148)) ) )).

tff(u28481,axiom,(
    ! [X75,X74] :
      ( k1_tarski(X74) = k4_xboole_0(k1_tarski(X74),k3_xboole_0(k1_tarski(X75),k1_tarski(X74)))
      | k1_xboole_0 = k1_tarski(X74)
      | k1_xboole_0 = k1_tarski(X75)
      | k1_tarski(X74) = k1_tarski(X75) ) )).

tff(u28480,axiom,(
    ! [X51,X52] :
      ( k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X51),k1_tarski(X52)))
      | k1_xboole_0 = k1_tarski(X52)
      | k1_tarski(X51) = k3_xboole_0(k1_tarski(X52),k1_tarski(X51)) ) )).

tff(u28479,axiom,(
    ! [X81,X80] :
      ( k1_tarski(X80) = k4_xboole_0(k1_tarski(X80),k3_xboole_0(k1_tarski(X81),k1_tarski(X80)))
      | k1_xboole_0 = k1_tarski(X80)
      | k1_tarski(X81) = k3_xboole_0(k1_tarski(X81),k1_tarski(X80)) ) )).

tff(u28478,axiom,(
    ! [X77,X76] :
      ( k1_tarski(X76) = k4_xboole_0(k1_tarski(X76),k3_xboole_0(k1_tarski(X77),k1_tarski(X76)))
      | k1_xboole_0 = k1_tarski(X76)
      | k1_tarski(X76) = k1_tarski(X77) ) )).

tff(u28477,axiom,(
    ! [X53,X52] :
      ( k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X52),k1_tarski(X53)))
      | k1_xboole_0 = k1_tarski(X52)
      | k1_tarski(X53) = k3_xboole_0(k1_tarski(X53),k1_tarski(X52)) ) )).

tff(u28476,axiom,(
    ! [X84,X85] :
      ( k1_tarski(X85) = k4_xboole_0(k1_tarski(X85),k3_xboole_0(k1_tarski(X85),k1_tarski(X84)))
      | k1_xboole_0 = k1_tarski(X85)
      | k1_tarski(X84) = k3_xboole_0(k1_tarski(X85),k1_tarski(X84)) ) )).

tff(u28475,axiom,(
    ! [X11,X10] :
      ( k1_tarski(X11) = k4_xboole_0(k1_tarski(X11),k3_xboole_0(k1_tarski(X11),k1_tarski(X10)))
      | k1_xboole_0 = k1_tarski(X11)
      | k1_tarski(X11) = k1_tarski(X10) ) )).

tff(u28474,axiom,(
    ! [X34,X35] :
      ( k1_tarski(X34) = k4_xboole_0(k1_tarski(X34),k3_xboole_0(X35,k1_tarski(X34)))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X34),X35) ) )).

tff(u28473,axiom,(
    ! [X62,X61] :
      ( k1_tarski(X61) = k4_xboole_0(k1_tarski(X61),k3_xboole_0(X62,k1_tarski(X61)))
      | k1_tarski(X61) = k3_xboole_0(k1_tarski(X61),X62) ) )).

tff(u28472,axiom,(
    ! [X63,X64] :
      ( k1_tarski(X63) = k4_xboole_0(k1_tarski(X63),k3_xboole_0(X64,k1_tarski(X63)))
      | k1_tarski(X63) = k3_xboole_0(X64,k1_tarski(X63)) ) )).

tff(u28471,axiom,(
    ! [X27,X28] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X27),k3_xboole_0(k1_tarski(X27),X28))
      | k1_tarski(X27) = k4_xboole_0(k1_tarski(X27),k3_xboole_0(X28,k1_tarski(X27))) ) )).

tff(u28470,axiom,(
    ! [X89,X88] :
      ( k1_tarski(X88) = k4_xboole_0(k1_tarski(X88),k3_xboole_0(X89,k1_tarski(X88)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X88))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X88),X89)) ) )).

tff(u28469,axiom,(
    ! [X18,X19] :
      ( k1_tarski(X18) = k4_xboole_0(k1_tarski(X18),k3_xboole_0(X19,k1_tarski(X18)))
      | k1_xboole_0 = k1_tarski(X18)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X18),X19)) ) )).

tff(u28468,axiom,(
    ! [X108,X107] :
      ( k1_tarski(X107) = k4_xboole_0(k1_tarski(X107),k3_xboole_0(X108,k1_tarski(X107)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X107),X108)) ) )).

tff(u28467,axiom,(
    ! [X81,X80] :
      ( k1_tarski(X80) = k4_xboole_0(k1_tarski(X80),k4_xboole_0(k1_tarski(X80),X81))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X80))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X80),X81)) ) )).

tff(u28466,axiom,(
    ! [X11,X10] :
      ( k1_tarski(X10) = k4_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))
      | k1_xboole_0 = k1_tarski(X10)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X10),X11)) ) )).

tff(u28465,axiom,(
    ! [X96,X97] :
      ( k1_tarski(X96) = k4_xboole_0(k1_tarski(X96),k4_xboole_0(k1_tarski(X96),X97))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X96),X97)) ) )).

tff(u28464,axiom,(
    ! [X56,X57] :
      ( k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),k4_xboole_0(k1_tarski(X56),X57))
      | k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),X57) ) )).

tff(u28463,axiom,(
    ! [X53,X52] :
      ( k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k4_xboole_0(k1_tarski(X52),X53))
      | k1_xboole_0 = k3_xboole_0(X53,k1_tarski(X52)) ) )).

tff(u28462,axiom,(
    ! [X31,X30] :
      ( k1_tarski(X30) = k4_xboole_0(k1_tarski(X30),k4_xboole_0(k1_tarski(X30),X31))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X30),X31) ) )).

tff(u28461,axiom,(
    ! [X22,X21] :
      ( k1_tarski(X21) = k4_xboole_0(k1_tarski(X21),k1_tarski(X22))
      | k1_tarski(X21) = k1_tarski(X22) ) )).

tff(u28460,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u28459,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) )).

tff(u28458,axiom,(
    ! [X7,X8] :
      ( k4_xboole_0(X7,k1_tarski(X8)) = k5_xboole_0(X7,k1_tarski(X8))
      | k1_xboole_0 = k3_xboole_0(X7,k1_tarski(X8)) ) )).

tff(u28457,axiom,(
    ! [X16,X15] :
      ( k4_xboole_0(X16,k1_tarski(X15)) = k5_xboole_0(X16,k1_tarski(X15))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X15),X16) ) )).

tff(u28456,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u28455,axiom,(
    ! [X7,X6] : k3_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X6,X7)) )).

tff(u28454,axiom,(
    ! [X18,X17] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X17,X18)) )).

tff(u28453,axiom,(
    ! [X62,X61] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X62),k1_tarski(X61)),k1_xboole_0)
      | k1_tarski(X61) = k1_tarski(X62) ) )).

tff(u28452,axiom,(
    ! [X190,X189] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X189),X190),k1_xboole_0)
      | k1_tarski(X189) = k3_xboole_0(X190,k1_tarski(X189)) ) )).

tff(u28451,axiom,(
    ! [X139,X138] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X138),X139),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X138),X139)) ) )).

tff(u28450,axiom,(
    ! [X53,X54] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X54),X53),k1_xboole_0)
      | k1_tarski(X54) = k3_xboole_0(k1_tarski(X54),X53) ) )).

tff(u28449,axiom,(
    ! [X63,X62] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X62),X63),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X62),X63) ) )).

tff(u28448,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X7),X8)) ) )).

tff(u28447,axiom,(
    ! [X102,X101] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X102,k1_tarski(X101)),k1_xboole_0)
      | k1_tarski(X101) = k3_xboole_0(k1_tarski(X101),X102) ) )).

tff(u28446,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X50,k1_tarski(X49)),k1_xboole_0)
      | k1_tarski(X49) = k3_xboole_0(X50,k1_tarski(X49)) ) )).

tff(u28445,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28444,axiom,(
    ! [X133,X132] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X133,k1_tarski(X132)),k1_tarski(X132))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X132),X133)) ) )).

tff(u28443,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_tarski(X7))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7))) ) )).

tff(u28442,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_tarski(X7))
      | k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28441,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X52,k1_tarski(X51)),k1_tarski(X51))
      | k1_xboole_0 = k3_xboole_0(X52,k1_tarski(X51)) ) )).

tff(u28440,axiom,(
    ! [X48,X47] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X48,k1_tarski(X47)),k1_tarski(X47))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X47),X48) ) )).

tff(u28439,axiom,(
    ! [X155,X156] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X155),X156),k1_tarski(X155))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X156,k1_tarski(X155))) ) )).

tff(u28438,axiom,(
    ! [X117,X118] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X117),X118),k1_tarski(X117))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X117),X118)) ) )).

tff(u28437,axiom,(
    ! [X89,X90] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X89),X90),k1_tarski(X89))
      | k1_tarski(X89) = k4_xboole_0(k1_tarski(X89),X90) ) )).

tff(u28436,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X50),X49),k1_tarski(X50))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X50),X49) ) )).

tff(u28435,axiom,(
    ! [X48,X47] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X48),X47),k1_tarski(X48))
      | k1_xboole_0 = k3_xboole_0(X47,k1_tarski(X48)) ) )).

tff(u28434,axiom,(
    ! [X65,X64] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X65),k1_tarski(X64)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X64))
      | k1_tarski(X65) = k3_xboole_0(k1_tarski(X64),k1_tarski(X65)) ) )).

tff(u28433,axiom,(
    ! [X63,X64] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X64),k1_tarski(X63)))
      | k1_tarski(X63) = k1_tarski(X64) ) )).

tff(u28432,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X0),X1))
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) )).

tff(u28431,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X0),X1))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X0))
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) )).

tff(u28430,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X12),X13))
      | k1_xboole_0 = k1_tarski(X12)
      | k1_tarski(X12) = k3_xboole_0(X13,k1_tarski(X12)) ) )).

tff(u28429,axiom,(
    ! [X29,X28] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X28),X29))
      | k1_tarski(X28) = k3_xboole_0(X29,k1_tarski(X28)) ) )).

tff(u28428,axiom,(
    ! [X55,X56] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X56),X55))
      | k1_tarski(X56) = k3_xboole_0(k1_tarski(X56),X55) ) )).

tff(u28427,axiom,(
    ! [X65,X64] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X64),X65))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X64),X65) ) )).

tff(u28426,axiom,(
    ! [X104,X103] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X104,k1_tarski(X103)))
      | k1_tarski(X103) = k3_xboole_0(k1_tarski(X103),X104) ) )).

tff(u28425,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X52,k1_tarski(X51)))
      | k1_tarski(X51) = k3_xboole_0(X52,k1_tarski(X51)) ) )).

tff(u28424,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7)))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28423,axiom,(
    ! [X58,X57] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X57),X58))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X58,k1_tarski(X57))) ) )).

tff(u28422,axiom,(
    ! [X141,X140] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X140),X141))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X140),X141)) ) )).

tff(u28421,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X12),X13))
      | k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28420,axiom,(
    ! [X95,X94] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X94),X95))
      | k1_xboole_0 = k3_xboole_0(X95,k1_tarski(X94)) ) )).

tff(u28419,axiom,(
    ! [X73,X72] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X72),X73))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X72),X73) ) )).

tff(u28418,axiom,(
    ! [X137,X136] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X136),X137),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X136),X137)) ) )).

tff(u28417,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0)
      | k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28416,axiom,(
    ! [X93,X92] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X92),X93),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(X93,k1_tarski(X92)) ) )).

tff(u28415,axiom,(
    ! [X71,X70] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X70),X71),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X70),X71) ) )).

tff(u28414,axiom,(
    ! [X60,X61] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X60),X61),k1_tarski(X60))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61)) ) )).

tff(u28413,axiom,(
    ! [X42,X41] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X41),X42),k1_tarski(X41))
      | k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41)) ) )).

tff(u28412,axiom,(
    ! [X46,X47] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X46),X47),k1_tarski(X46))
      | k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47) ) )).

tff(u28411,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_tarski(X12))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28410,axiom,(
    ! [X20,X21] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X21),k1_tarski(X20))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X21),k1_tarski(X20)) ) )).

tff(u28409,axiom,(
    ! [X20,X21] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X20),k1_tarski(X21))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X21),k1_tarski(X20)) ) )).

tff(u28408,axiom,(
    ! [X166,X167] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X166),k3_xboole_0(X167,k1_tarski(X166)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X166),X167)) ) )).

tff(u28407,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7))) ) )).

tff(u28406,axiom,(
    ! [X7,X8] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))
      | k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28405,axiom,(
    ! [X53,X54] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X53),k3_xboole_0(X54,k1_tarski(X53)))
      | k1_xboole_0 = k3_xboole_0(X54,k1_tarski(X53)) ) )).

tff(u28404,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X49),k3_xboole_0(X50,k1_tarski(X49)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X49),X50) ) )).

tff(u28403,axiom,(
    ! [X197,X198] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X197),k3_xboole_0(k1_tarski(X197),X198))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X198,k1_tarski(X197))) ) )).

tff(u28402,axiom,(
    ! [X151,X152] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X151),k3_xboole_0(k1_tarski(X151),X152))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X151),X152)) ) )).

tff(u28401,axiom,(
    ! [X124,X123] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X123),k3_xboole_0(k1_tarski(X123),X124))
      | k1_tarski(X123) = k4_xboole_0(k1_tarski(X123),X124) ) )).

tff(u28400,axiom,(
    ! [X51,X52] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X52),X51))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X52),X51) ) )).

tff(u28399,axiom,(
    ! [X49,X50] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X50),k3_xboole_0(k1_tarski(X50),X49))
      | k1_xboole_0 = k3_xboole_0(X49,k1_tarski(X50)) ) )).

tff(u28398,axiom,(
    ! [X60,X61] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X60),k4_xboole_0(k1_tarski(X60),X61))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61)) ) )).

tff(u28397,axiom,(
    ! [X42,X41] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X41),k4_xboole_0(k1_tarski(X41),X42))
      | k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41)) ) )).

tff(u28396,axiom,(
    ! [X46,X47] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X46),k4_xboole_0(k1_tarski(X46),X47))
      | k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47) ) )).

tff(u28395,axiom,(
    ! [X13,X12] :
      ( k1_xboole_0 = k5_xboole_0(k1_tarski(X12),k4_xboole_0(k1_tarski(X12),X13))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28394,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u28393,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) )).

tff(u28392,negated_conjecture,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 = k1_tarski(sK0) )).

tff(u28391,axiom,(
    ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) )).

tff(u28390,axiom,(
    ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

tff(u28389,axiom,(
    ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

tff(u28388,axiom,(
    ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

tff(u28387,axiom,(
    ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) )).

tff(u28386,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u28385,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u28384,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u28383,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u28382,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u28381,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) )).

tff(u28380,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u28379,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X2,X1),X1) )).

tff(u28378,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X2),X1)
      | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X2)) ) )).

tff(u28377,axiom,(
    ! [X9,X10] :
      ( r1_tarski(k1_tarski(X9),X10)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X9),X10) ) )).

tff(u28376,axiom,(
    ! [X1,X0] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) )).

tff(u28375,axiom,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),k3_xboole_0(X12,X11)) )).

tff(u28374,axiom,(
    ! [X126,X127] :
      ( r1_tarski(k1_tarski(X126),k3_xboole_0(X127,k1_tarski(X126)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X126),X127)) ) )).

tff(u28373,axiom,(
    ! [X7,X8] :
      ( r1_tarski(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7))) ) )).

tff(u28372,axiom,(
    ! [X7,X8] :
      ( r1_tarski(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))
      | k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28371,axiom,(
    ! [X36,X35] :
      ( r1_tarski(k1_tarski(X35),k3_xboole_0(X36,k1_tarski(X35)))
      | k1_xboole_0 = k3_xboole_0(X36,k1_tarski(X35)) ) )).

tff(u28370,axiom,(
    ! [X32,X31] :
      ( r1_tarski(k1_tarski(X31),k3_xboole_0(X32,k1_tarski(X31)))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X31),X32) ) )).

tff(u28369,axiom,(
    ! [X150,X149] :
      ( r1_tarski(k1_tarski(X149),k3_xboole_0(k1_tarski(X149),X150))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X150,k1_tarski(X149))) ) )).

tff(u28368,axiom,(
    ! [X112,X111] :
      ( r1_tarski(k1_tarski(X111),k3_xboole_0(k1_tarski(X111),X112))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X111),X112)) ) )).

tff(u28367,axiom,(
    ! [X84,X83] :
      ( r1_tarski(k1_tarski(X83),k3_xboole_0(k1_tarski(X83),X84))
      | k1_tarski(X83) = k4_xboole_0(k1_tarski(X83),X84) ) )).

tff(u28366,axiom,(
    ! [X34,X33] :
      ( r1_tarski(k1_tarski(X34),k3_xboole_0(k1_tarski(X34),X33))
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X34),X33) ) )).

tff(u28365,axiom,(
    ! [X32,X31] :
      ( r1_tarski(k1_tarski(X32),k3_xboole_0(k1_tarski(X32),X31))
      | k1_xboole_0 = k3_xboole_0(X31,k1_tarski(X32)) ) )).

tff(u28364,axiom,(
    ! [X48,X47] :
      ( r1_tarski(k3_xboole_0(k1_tarski(X48),k1_tarski(X47)),k1_xboole_0)
      | k1_tarski(X47) = k1_tarski(X48) ) )).

tff(u28363,axiom,(
    ! [X7,X8] :
      ( r1_tarski(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X7),X8)) ) )).

tff(u28362,axiom,(
    ! [X87,X88] :
      ( r1_tarski(k3_xboole_0(X88,k1_tarski(X87)),k1_xboole_0)
      | k1_tarski(X87) = k3_xboole_0(k1_tarski(X87),X88) ) )).

tff(u28361,axiom,(
    ! [X7,X8] :
      ( r1_tarski(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8) ) )).

tff(u28360,axiom,(
    ! [X36,X35] :
      ( r1_tarski(k3_xboole_0(X36,k1_tarski(X35)),k1_xboole_0)
      | k1_tarski(X35) = k3_xboole_0(X36,k1_tarski(X35)) ) )).

tff(u28359,axiom,(
    ! [X176,X175] :
      ( r1_tarski(k3_xboole_0(k1_tarski(X175),X176),k1_xboole_0)
      | k1_tarski(X175) = k3_xboole_0(X176,k1_tarski(X175)) ) )).

tff(u28358,axiom,(
    ! [X124,X125] :
      ( r1_tarski(k3_xboole_0(k1_tarski(X124),X125),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X124),X125)) ) )).

tff(u28357,axiom,(
    ! [X49,X48] :
      ( r1_tarski(k3_xboole_0(k1_tarski(X48),X49),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X48),X49) ) )).

tff(u28356,axiom,(
    ! [X40,X39] :
      ( r1_tarski(k3_xboole_0(k1_tarski(X40),X39),k1_xboole_0)
      | k1_tarski(X40) = k3_xboole_0(k1_tarski(X40),X39) ) )).

tff(u28355,axiom,(
    ! [X58,X57] :
      ( r1_tarski(k4_xboole_0(k1_tarski(X57),X58),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X58,k1_tarski(X57))) ) )).

tff(u28354,axiom,(
    ! [X53,X52] :
      ( r1_tarski(k4_xboole_0(k1_tarski(X52),X53),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X52),X53)) ) )).

tff(u28353,axiom,(
    ! [X18,X17] :
      ( r1_tarski(k4_xboole_0(k1_tarski(X17),X18),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(X18,k1_tarski(X17)) ) )).

tff(u28352,axiom,(
    ! [X20,X21] :
      ( r1_tarski(k4_xboole_0(k1_tarski(X20),X21),k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X20),X21) ) )).

tff(u28351,axiom,(
    ! [X13,X12] :
      ( r1_tarski(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0)
      | k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13) ) )).

tff(u28350,axiom,(
    ! [X65,X64] :
      ( r1_tarski(k1_tarski(X64),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X65),k1_tarski(X64)))
      | k1_tarski(X65) = k3_xboole_0(k1_tarski(X64),k1_tarski(X65)) ) )).

tff(u28349,axiom,(
    ! [X91,X90] :
      ( r1_tarski(k1_tarski(X90),k1_xboole_0)
      | k1_tarski(X90) = k3_xboole_0(X91,k1_tarski(X90))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X90),X91)) ) )).

tff(u28348,axiom,(
    ! [X60,X61] :
      ( r1_tarski(k1_tarski(X60),k4_xboole_0(k1_tarski(X60),X61))
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61)) ) )).

tff(u28347,axiom,(
    ! [X42,X41] :
      ( r1_tarski(k1_tarski(X41),k4_xboole_0(k1_tarski(X41),X42))
      | k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41)) ) )).

tff(u28346,axiom,(
    ! [X46,X47] :
      ( r1_tarski(k1_tarski(X46),k4_xboole_0(k1_tarski(X46),X47))
      | k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47) ) )).

tff(u28345,axiom,(
    ! [X18,X19] :
      ( r1_tarski(k1_tarski(X18),k4_xboole_0(k1_tarski(X18),X19))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X18),X19) ) )).

tff(u28344,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u28343,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) )).

tff(u28342,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) )).

tff(u28341,axiom,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X0) ) )).

tff(u28340,axiom,(
    ! [X7,X6] :
      ( ~ r2_hidden(X6,X7)
      | k1_tarski(X6) = k3_xboole_0(k1_tarski(X6),X7) ) )).

tff(u28339,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )).

tff(u28338,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) )).

tff(u28337,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) )).

tff(u28336,negated_conjecture,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ! [X1] :
        ( r2_hidden(sK0,X1)
        | r1_xboole_0(k1_xboole_0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (3978)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (3966)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (3969)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (3973)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (3971)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (3974)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (3976)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (3968)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (3979)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (3970)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (3967)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (3983)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (3982)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (3980)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (3977)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (3977)Refutation not found, incomplete strategy% (3977)------------------------------
% 0.21/0.50  % (3977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3977)Memory used [KB]: 10618
% 0.21/0.50  % (3977)Time elapsed: 0.091 s
% 0.21/0.50  % (3977)------------------------------
% 0.21/0.50  % (3977)------------------------------
% 0.21/0.51  % (3975)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (3972)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3981)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.09/1.03  % (3970)Time limit reached!
% 5.09/1.03  % (3970)------------------------------
% 5.09/1.03  % (3970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.03  % (3970)Termination reason: Time limit
% 5.09/1.03  % (3970)Termination phase: Saturation
% 5.09/1.03  
% 5.09/1.03  % (3970)Memory used [KB]: 9850
% 5.09/1.03  % (3970)Time elapsed: 0.600 s
% 5.09/1.03  % (3970)------------------------------
% 5.09/1.03  % (3970)------------------------------
% 8.11/1.40  % SZS status CounterSatisfiable for theBenchmark
% 8.11/1.40  % (3982)# SZS output start Saturation.
% 8.11/1.40  tff(u28642,axiom,
% 8.11/1.40      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28641,axiom,
% 8.11/1.40      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28640,axiom,
% 8.11/1.40      (![X6] : ((k4_xboole_0(X6,k1_xboole_0) = X6)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28639,axiom,
% 8.11/1.40      (![X13, X14] : (((k4_xboole_0(X13,k1_tarski(X14)) = X13) | (k1_tarski(X14) = k3_xboole_0(k1_tarski(X14),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28638,axiom,
% 8.11/1.40      (![X18, X17] : (((k4_xboole_0(X18,k1_tarski(X17)) = X18) | (k1_tarski(X17) = k3_xboole_0(X18,k1_tarski(X17))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28637,axiom,
% 8.11/1.40      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28636,axiom,
% 8.11/1.40      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28635,axiom,
% 8.11/1.40      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28634,axiom,
% 8.11/1.40      (![X11, X10] : ((k4_xboole_0(X10,X11) = k3_xboole_0(k4_xboole_0(X10,X11),X10))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28633,axiom,
% 8.11/1.40      (![X5, X4] : ((k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28632,axiom,
% 8.11/1.40      (![X1, X2] : (((k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X1),X2)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28631,axiom,
% 8.11/1.40      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28630,axiom,
% 8.11/1.40      (![X3, X4] : ((k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28629,axiom,
% 8.11/1.40      (![X29, X30] : ((k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X30,X29),k3_xboole_0(X29,X30)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28628,axiom,
% 8.11/1.40      (![X7, X8] : ((k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X8,X7)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28627,axiom,
% 8.11/1.40      (![X15, X14] : ((k3_xboole_0(X15,X14) = k3_xboole_0(k3_xboole_0(X15,X14),k3_xboole_0(X14,X15)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28626,axiom,
% 8.11/1.40      (![X84, X83] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X83),k3_xboole_0(k1_tarski(X83),X84))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X83))) | (k1_tarski(X83) = k3_xboole_0(X84,k1_tarski(X83))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28625,axiom,
% 8.11/1.40      (![X40, X39] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X39),k3_xboole_0(k1_tarski(X39),X40))) | (k1_tarski(X39) = k3_xboole_0(X40,k1_tarski(X39))) | (k1_xboole_0 = k1_tarski(X39)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28624,axiom,
% 8.11/1.40      (![X150, X151] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X150),k3_xboole_0(k1_tarski(X150),X151))) | (k1_tarski(X150) = k3_xboole_0(X151,k1_tarski(X150))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28623,axiom,
% 8.11/1.40      (![X16, X15] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X15),k3_xboole_0(k1_tarski(X15),X16))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X15),X16))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28622,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X51),k3_xboole_0(k1_tarski(X51),X52))) | (k1_tarski(X51) = k3_xboole_0(k1_tarski(X51),X52)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28621,axiom,
% 8.11/1.40      (![X5, X6] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),X6))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X5),X6)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28620,axiom,
% 8.11/1.40      (![X34, X35] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X35),k3_xboole_0(k1_tarski(X34),k1_tarski(X35)))) | (k1_tarski(X34) = k3_xboole_0(k1_tarski(X35),k1_tarski(X34))) | (k1_xboole_0 = k1_tarski(X35)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28619,axiom,
% 8.11/1.40      (![X29, X28] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X29),k3_xboole_0(k1_tarski(X28),k1_tarski(X29)))) | (k1_tarski(X28) = k3_xboole_0(k1_tarski(X28),k1_tarski(X29))) | (k1_xboole_0 = k1_tarski(X29)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28618,axiom,
% 8.11/1.40      (![X25, X24] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X25),k3_xboole_0(k1_tarski(X24),k1_tarski(X25)))) | (k1_tarski(X25) = k1_tarski(X24)) | (k1_xboole_0 = k1_tarski(X25)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28617,axiom,
% 8.11/1.40      (![X18, X17] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k3_xboole_0(k1_tarski(X17),k1_tarski(X18)))) | (k1_tarski(X18) = k3_xboole_0(k1_tarski(X18),k1_tarski(X17))) | (k1_xboole_0 = k1_tarski(X17)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28616,axiom,
% 8.11/1.40      (![X25, X26] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X26),k3_xboole_0(k1_tarski(X26),k1_tarski(X25)))) | (k1_tarski(X25) = k3_xboole_0(k1_tarski(X26),k1_tarski(X25))) | (k1_xboole_0 = k1_tarski(X26)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28615,axiom,
% 8.11/1.40      (![X13, X14] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X13),k3_xboole_0(k1_tarski(X13),k1_tarski(X14)))) | (k1_tarski(X13) = k1_tarski(X14)) | (k1_xboole_0 = k1_tarski(X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28614,axiom,
% 8.11/1.40      (![X18, X17] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k3_xboole_0(X18,k1_tarski(X17)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X17),X18))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28613,axiom,
% 8.11/1.40      (![X55, X56] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X55),k3_xboole_0(X56,k1_tarski(X55)))) | (k1_tarski(X55) = k3_xboole_0(X56,k1_tarski(X55))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28612,axiom,
% 8.11/1.40      (![X53, X54] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X53),k3_xboole_0(X54,k1_tarski(X53)))) | (k1_tarski(X53) = k3_xboole_0(k1_tarski(X53),X54)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28611,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28610,axiom,
% 8.11/1.40      (![X5, X6] : (((k1_tarski(X5) = k3_xboole_0(k1_tarski(X5),k3_xboole_0(X6,k1_tarski(X5)))) | (k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),X6)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28609,axiom,
% 8.11/1.40      (![X46, X45] : (((k1_tarski(X45) = k3_xboole_0(k1_tarski(X45),k3_xboole_0(X46,k1_tarski(X45)))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X45),X46)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28608,axiom,
% 8.11/1.40      (![X16, X17] : (((k1_tarski(X17) = k3_xboole_0(k1_tarski(X17),k3_xboole_0(X16,k1_tarski(X17)))) | (k1_xboole_0 = k3_xboole_0(X16,k1_tarski(X17))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28607,axiom,
% 8.11/1.40      (![X29, X28] : (((k1_tarski(X29) = k3_xboole_0(k1_tarski(X29),k3_xboole_0(X28,k1_tarski(X29)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X28,k1_tarski(X29)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28606,axiom,
% 8.11/1.40      (![X29, X28] : (((k1_tarski(X28) = k3_xboole_0(k1_tarski(X28),k3_xboole_0(X29,k1_tarski(X28)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X28),X29))) | (k1_xboole_0 = k1_tarski(X28)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28605,axiom,
% 8.11/1.40      (![X95, X94] : (((k1_tarski(X94) = k3_xboole_0(k1_tarski(X94),k3_xboole_0(X95,k1_tarski(X94)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X94))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X94),X95))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28604,axiom,
% 8.11/1.40      (![X106, X105] : (((k1_tarski(X105) = k3_xboole_0(k1_tarski(X105),k3_xboole_0(X106,k1_tarski(X105)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X105),X106))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28603,axiom,
% 8.11/1.40      (![X11, X10] : (((k1_tarski(X10) = k3_xboole_0(k1_tarski(X10),k3_xboole_0(k1_tarski(X10),X11))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X11,k1_tarski(X10)))) | (k1_xboole_0 = k1_tarski(X10)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28602,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_tarski(X37) = k3_xboole_0(k1_tarski(X37),k3_xboole_0(k1_tarski(X37),X38))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X38,k1_tarski(X37)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28601,axiom,
% 8.11/1.40      (![X20, X19] : (((k1_tarski(X19) = k3_xboole_0(k1_tarski(X19),k3_xboole_0(k1_tarski(X19),X20))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X19),X20))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28600,axiom,
% 8.11/1.40      (![X3, X4] : (((k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),X4))) | (k1_tarski(X3) = k4_xboole_0(k1_tarski(X3),X4)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28599,axiom,
% 8.11/1.40      (![X48, X47] : (((k1_tarski(X48) = k3_xboole_0(k1_tarski(X48),k3_xboole_0(k1_tarski(X48),X47))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X48),X47)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28598,axiom,
% 8.11/1.40      (![X46, X45] : (((k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),k3_xboole_0(k1_tarski(X46),X45))) | (k1_xboole_0 = k3_xboole_0(X45,k1_tarski(X46))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28597,axiom,
% 8.11/1.40      (![X1] : ((k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28596,axiom,
% 8.11/1.40      (![X3, X2] : ((k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28595,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X20),X21))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28594,axiom,
% 8.11/1.40      (![X58, X59] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X58),k4_xboole_0(k1_tarski(X58),X59))) | (k1_tarski(X58) = k4_xboole_0(k1_tarski(X58),X59)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28593,axiom,
% 8.11/1.40      (![X18, X17] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X17),k4_xboole_0(k1_tarski(X17),X18))) | (k1_xboole_0 = k3_xboole_0(X18,k1_tarski(X17))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28592,axiom,
% 8.11/1.40      (![X11, X10] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X10),X11)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28591,axiom,
% 8.11/1.40      (![X16, X17] : (((k1_tarski(X16) = k3_xboole_0(k1_tarski(X16),k4_xboole_0(k1_tarski(X16),X17))) | (k1_tarski(X16) = k3_xboole_0(X17,k1_tarski(X16))) | (k1_xboole_0 = k1_tarski(X16)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28590,axiom,
% 8.11/1.40      (![X22, X23] : (((k1_tarski(X22) = k3_xboole_0(k1_tarski(X22),k4_xboole_0(k1_tarski(X22),X23))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X22),X23))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28589,axiom,
% 8.11/1.40      (![X71, X70] : (((k1_tarski(X70) = k3_xboole_0(k1_tarski(X70),k4_xboole_0(k1_tarski(X70),X71))) | (k1_tarski(X70) = k3_xboole_0(X71,k1_tarski(X70))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28588,axiom,
% 8.11/1.40      (![X9, X8] : (((k1_tarski(X8) = k3_xboole_0(k1_tarski(X8),k4_xboole_0(k1_tarski(X8),X9))) | (k1_tarski(X8) = k3_xboole_0(k1_tarski(X8),X9)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28587,axiom,
% 8.11/1.40      (![X11, X10] : (((k1_tarski(X10) = k3_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X10),X11)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28586,axiom,
% 8.11/1.40      (![X3, X4] : (((k1_tarski(X3) = k3_xboole_0(X4,k1_tarski(X3))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X3),X4)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28585,axiom,
% 8.11/1.40      (![X3, X4] : (((k1_tarski(X3) = k3_xboole_0(X4,k1_tarski(X3))) | (k1_xboole_0 = k3_xboole_0(X4,k1_tarski(X3))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28584,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_tarski(X41) = k3_xboole_0(k3_xboole_0(X42,k1_tarski(X41)),k1_tarski(X41))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X41),X42)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28583,axiom,
% 8.11/1.40      (![X13, X14] : (((k1_tarski(X13) = k3_xboole_0(k3_xboole_0(X14,k1_tarski(X13)),k1_tarski(X13))) | (k1_xboole_0 = k3_xboole_0(X14,k1_tarski(X13))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28582,axiom,
% 8.11/1.40      (![X16, X15] : (((k1_tarski(X15) = k3_xboole_0(k3_xboole_0(X16,k1_tarski(X15)),k1_tarski(X15))) | (k1_tarski(X15) = k4_xboole_0(k1_tarski(X15),X16)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28581,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_tarski(X20) = k3_xboole_0(k3_xboole_0(X21,k1_tarski(X20)),k1_tarski(X20))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X20),X21))) | (k1_xboole_0 = k1_tarski(X20)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28580,axiom,
% 8.11/1.40      (![X98, X99] : (((k1_tarski(X98) = k3_xboole_0(k3_xboole_0(X99,k1_tarski(X98)),k1_tarski(X98))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X98))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X98),X99))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28579,axiom,
% 8.11/1.40      (![X22, X23] : (((k1_tarski(X22) = k3_xboole_0(k3_xboole_0(X23,k1_tarski(X22)),k1_tarski(X22))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X23,k1_tarski(X22)))) | (k1_xboole_0 = k1_tarski(X22)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28578,axiom,
% 8.11/1.40      (![X100, X101] : (((k1_tarski(X100) = k3_xboole_0(k3_xboole_0(X101,k1_tarski(X100)),k1_tarski(X100))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X100))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X101,k1_tarski(X100)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28577,axiom,
% 8.11/1.40      (![X141, X140] : (((k1_tarski(X140) = k3_xboole_0(k3_xboole_0(X141,k1_tarski(X140)),k1_tarski(X140))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X141,k1_tarski(X140)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28576,axiom,
% 8.11/1.40      (![X145, X144] : (((k1_tarski(X144) = k3_xboole_0(k3_xboole_0(X145,k1_tarski(X144)),k1_tarski(X144))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X144),X145))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28575,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_tarski(X42) = k3_xboole_0(k3_xboole_0(k1_tarski(X42),X41),k1_tarski(X42))) | (k1_xboole_0 = k3_xboole_0(X41,k1_tarski(X42))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28574,axiom,
% 8.11/1.40      (![X9, X10] : (((k1_tarski(X9) = k3_xboole_0(k3_xboole_0(k1_tarski(X9),X10),k1_tarski(X9))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X9),X10)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28573,axiom,
% 8.11/1.40      (![X13, X14] : (((k1_tarski(X13) = k3_xboole_0(k3_xboole_0(k1_tarski(X13),X14),k1_tarski(X13))) | (k1_tarski(X13) = k4_xboole_0(k1_tarski(X13),X14)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28572,axiom,
% 8.11/1.40      (![X18, X19] : (((k1_tarski(X18) = k3_xboole_0(k3_xboole_0(k1_tarski(X18),X19),k1_tarski(X18))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X18),X19))) | (k1_xboole_0 = k1_tarski(X18)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28571,axiom,
% 8.11/1.40      (![X96, X97] : (((k1_tarski(X96) = k3_xboole_0(k3_xboole_0(k1_tarski(X96),X97),k1_tarski(X96))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X96))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X96),X97))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28570,axiom,
% 8.11/1.40      (![X129, X130] : (((k1_tarski(X129) = k3_xboole_0(k3_xboole_0(k1_tarski(X129),X130),k1_tarski(X129))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X129),X130))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28569,axiom,
% 8.11/1.40      (![X16, X17] : (((k1_tarski(X17) = k3_xboole_0(k3_xboole_0(k1_tarski(X17),X16),k1_tarski(X17))) | (k1_xboole_0 = k1_tarski(X17)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X16,k1_tarski(X17)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28568,axiom,
% 8.11/1.40      (![X143, X142] : (((k1_tarski(X143) = k3_xboole_0(k3_xboole_0(k1_tarski(X143),X142),k1_tarski(X143))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X143))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X142,k1_tarski(X143)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28567,axiom,
% 8.11/1.40      (![X195, X194] : (((k1_tarski(X195) = k3_xboole_0(k3_xboole_0(k1_tarski(X195),X194),k1_tarski(X195))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X194,k1_tarski(X195)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28566,axiom,
% 8.11/1.40      (![X16, X17] : (((k1_tarski(X16) = k3_xboole_0(k4_xboole_0(k1_tarski(X16),X17),k1_tarski(X16))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X16),X17)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28565,axiom,
% 8.11/1.40      (![X18, X19] : (((k1_tarski(X18) = k3_xboole_0(k4_xboole_0(k1_tarski(X18),X19),k1_tarski(X18))) | (k1_tarski(X18) = k3_xboole_0(k1_tarski(X18),X19)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28564,axiom,
% 8.11/1.40      (![X27, X26] : (((k1_tarski(X26) = k3_xboole_0(k4_xboole_0(k1_tarski(X26),X27),k1_tarski(X26))) | (k1_xboole_0 = k1_tarski(X26)) | (k1_tarski(X26) = k3_xboole_0(X27,k1_tarski(X26))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28563,axiom,
% 8.11/1.40      (![X29, X28] : (((k1_tarski(X28) = k3_xboole_0(k4_xboole_0(k1_tarski(X28),X29),k1_tarski(X28))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X28))) | (k1_tarski(X28) = k3_xboole_0(X29,k1_tarski(X28))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28562,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_tarski(X49) = k3_xboole_0(k4_xboole_0(k1_tarski(X49),X50),k1_tarski(X49))) | (k1_tarski(X49) = k3_xboole_0(X50,k1_tarski(X49))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28561,axiom,
% 8.11/1.40      (![X15, X14] : (((k1_tarski(X14) = k3_xboole_0(k4_xboole_0(k1_tarski(X14),X15),k1_tarski(X14))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X14),X15))) | (k1_xboole_0 = k1_tarski(X14)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28560,axiom,
% 8.11/1.40      (![X93, X92] : (((k1_tarski(X92) = k3_xboole_0(k4_xboole_0(k1_tarski(X92),X93),k1_tarski(X92))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X92))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X92),X93))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28559,axiom,
% 8.11/1.40      (![X131, X130] : (((k1_tarski(X130) = k3_xboole_0(k4_xboole_0(k1_tarski(X130),X131),k1_tarski(X130))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X130),X131))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28558,axiom,
% 8.11/1.40      (![X3, X4] : (((k1_tarski(X4) = k3_xboole_0(k1_tarski(X4),X3)) | (k1_xboole_0 = k3_xboole_0(X3,k1_tarski(X4))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28557,axiom,
% 8.11/1.40      (![X18, X19] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X19),k1_tarski(X18))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X18),k1_tarski(X19))) | (k1_tarski(X18) = k1_tarski(X19)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28556,axiom,
% 8.11/1.40      (![X58, X59] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X58),k1_tarski(X59))) | (k1_xboole_0 = k1_tarski(X59)) | (k1_tarski(X58) = k1_tarski(X59)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28555,axiom,
% 8.11/1.40      (![X15, X14] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X14),k1_tarski(X15))) | (k1_xboole_0 = k1_tarski(X14)) | (k1_tarski(X15) = k1_tarski(X14)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28554,axiom,
% 8.11/1.40      (![X22, X23] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X23),k1_tarski(X22))) | (k1_tarski(X23) = k1_tarski(X22)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28553,axiom,
% 8.11/1.40      (![X25, X26] : (((k1_tarski(X25) = k3_xboole_0(k3_xboole_0(k1_tarski(X25),X26),k1_tarski(X25))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X26,k1_tarski(X25)),k1_tarski(X25))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28552,axiom,
% 8.11/1.40      (![X23, X24] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(X24,k1_tarski(X23)),k1_tarski(X23))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X23),X24))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28551,axiom,
% 8.11/1.40      (![X13, X14] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,k1_tarski(X13)),k1_tarski(X13))) | (k1_tarski(X13) = k3_xboole_0(k1_tarski(X13),X14)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28550,axiom,
% 8.11/1.40      (![X53, X54] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(X53,k1_tarski(X54)),k1_tarski(X54))) | (k1_tarski(X54) = k3_xboole_0(X53,k1_tarski(X54))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28549,axiom,
% 8.11/1.40      (![X9, X10] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(X10,k1_tarski(X9)),k1_tarski(X9))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X9),X10)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28548,axiom,
% 8.11/1.40      (![X73, X72] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X73),k1_tarski(X72)),k1_tarski(X72))) | (k1_xboole_0 = k1_tarski(X72)) | (k1_xboole_0 = k1_tarski(X73)) | (k1_tarski(X72) = k1_tarski(X73)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28547,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X38),k1_tarski(X37)),k1_tarski(X37))) | (k1_tarski(X38) = k3_xboole_0(k1_tarski(X37),k1_tarski(X38))) | (k1_xboole_0 = k1_tarski(X37)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28546,axiom,
% 8.11/1.40      (![X79, X78] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X79),k1_tarski(X78)),k1_tarski(X78))) | (k1_xboole_0 = k1_tarski(X78)) | (k1_tarski(X79) = k3_xboole_0(k1_tarski(X79),k1_tarski(X78))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28545,axiom,
% 8.11/1.40      (![X75, X74] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X75),k1_tarski(X74)),k1_tarski(X74))) | (k1_xboole_0 = k1_tarski(X74)) | (k1_tarski(X74) = k1_tarski(X75)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28544,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X51),X52),k1_tarski(X51))) | (k1_tarski(X51) = k3_xboole_0(k1_tarski(X51),X52)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28543,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X7),X8),k1_tarski(X7))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28542,axiom,
% 8.11/1.40      (![X22, X21] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X21),X22),k1_tarski(X21))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X21),X22))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28541,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X37),X38),k1_tarski(X37))) | (k1_tarski(X37) = k3_xboole_0(X38,k1_tarski(X37))) | (k1_xboole_0 = k1_tarski(X37)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28540,axiom,
% 8.11/1.40      (![X102, X101] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X101),X102),k1_tarski(X101))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X101))) | (k1_tarski(X101) = k3_xboole_0(X102,k1_tarski(X101))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28539,axiom,
% 8.11/1.40      (![X172, X171] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X171),X172),k1_tarski(X171))) | (k1_tarski(X171) = k3_xboole_0(X172,k1_tarski(X171))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28538,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X49),X50),k1_tarski(X49))) | (k1_tarski(X49) = k3_xboole_0(k3_xboole_0(X50,k1_tarski(X49)),k1_tarski(X49))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28537,axiom,
% 8.11/1.40      (![X25, X24] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X25),k1_tarski(X24)),k1_tarski(X25))) | (k1_tarski(X24) = k3_xboole_0(k1_tarski(X24),k1_tarski(X25))) | (k1_xboole_0 = k1_tarski(X25)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28536,axiom,
% 8.11/1.40      (![X95, X94] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X95),k1_tarski(X94)),k1_tarski(X95))) | (k1_xboole_0 = k1_tarski(X95)) | (k1_tarski(X94) = k3_xboole_0(k1_tarski(X95),k1_tarski(X94))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28535,axiom,
% 8.11/1.40      (![X23, X24] : (((k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_tarski(X24),k1_tarski(X23)),k1_tarski(X24))) | (k1_xboole_0 = k1_tarski(X24)) | (k1_tarski(X23) = k1_tarski(X24)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28534,axiom,
% 8.11/1.40      (![X27, X26] : (((k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X26),X27),k1_tarski(X26))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X26),X27))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28533,axiom,
% 8.11/1.40      (![X56, X57] : (((k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X56),X57),k1_tarski(X56))) | (k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),X57)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28532,axiom,
% 8.11/1.40      (![X22, X21] : (((k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X21),X22),k1_tarski(X21))) | (k1_xboole_0 = k3_xboole_0(X22,k1_tarski(X21))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28531,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k3_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_tarski(X12))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28530,axiom,
% 8.11/1.40      (![X1, X0] : ((k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28529,axiom,
% 8.11/1.40      (![X1] : ((k1_xboole_0 = k4_xboole_0(X1,X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28528,axiom,
% 8.11/1.40      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28527,axiom,
% 8.11/1.40      (![X1] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28526,axiom,
% 8.11/1.40      (![X15, X14] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28525,axiom,
% 8.11/1.40      (![X5, X4] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X4),X4))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28524,axiom,
% 8.11/1.40      (![X16, X15] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X16),X15)) | (k1_xboole_0 = k3_xboole_0(X15,k1_tarski(X16))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28523,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28522,axiom,
% 8.11/1.40      (![X23, X24] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X23)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28521,axiom,
% 8.11/1.40      (![X18, X17] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X17),k3_xboole_0(X18,k1_tarski(X17)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X18,k1_tarski(X17)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28520,axiom,
% 8.11/1.40      (![X16, X15] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X15),k3_xboole_0(X16,k1_tarski(X15)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X15),X16))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28519,axiom,
% 8.11/1.40      (![X22, X21] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X21),k3_xboole_0(X22,k1_tarski(X21)))) | (k1_tarski(X21) = k4_xboole_0(k1_tarski(X21),X22)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28518,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X41),k3_xboole_0(X42,k1_tarski(X41)))) | (k1_xboole_0 = k3_xboole_0(X42,k1_tarski(X41))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28517,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X37),k3_xboole_0(X38,k1_tarski(X37)))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X37),X38)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28516,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X38),k3_xboole_0(k1_tarski(X38),X37))) | (k1_xboole_0 = k3_xboole_0(X37,k1_tarski(X38))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28515,axiom,
% 8.11/1.40      (![X20, X19] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X19),k3_xboole_0(k1_tarski(X19),X20))) | (k1_tarski(X19) = k4_xboole_0(k1_tarski(X19),X20)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28514,axiom,
% 8.11/1.40      (![X40, X39] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X40),k3_xboole_0(k1_tarski(X40),X39))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X40),X39)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28513,axiom,
% 8.11/1.40      (![X13, X14] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X13),k3_xboole_0(k1_tarski(X13),X14))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X13),X14))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28512,axiom,
% 8.11/1.40      (![X91, X92] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X91),k3_xboole_0(k1_tarski(X91),X92))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X91))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X92,k1_tarski(X91)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28511,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X51),k3_xboole_0(k1_tarski(X51),X52))) | (k1_xboole_0 = k1_tarski(X51)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X52,k1_tarski(X51)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28510,axiom,
% 8.11/1.40      (![X164, X163] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X163),k3_xboole_0(k1_tarski(X163),X164))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X164,k1_tarski(X163)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28509,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X50),k1_tarski(X49)),k1_xboole_0)) | (k1_tarski(X49) = k1_tarski(X50)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28508,axiom,
% 8.11/1.40      (![X178, X177] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X177),X178),k1_xboole_0)) | (k1_tarski(X177) = k3_xboole_0(X178,k1_tarski(X177))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28507,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X42),X41),k1_xboole_0)) | (k1_tarski(X42) = k3_xboole_0(k1_tarski(X42),X41)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28506,axiom,
% 8.11/1.40      (![X51, X50] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_tarski(X50),X51),k1_xboole_0)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X50),X51)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28505,axiom,
% 8.11/1.40      (![X89, X90] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X90,k1_tarski(X89)),k1_xboole_0)) | (k1_tarski(X89) = k3_xboole_0(k1_tarski(X89),X90)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28504,axiom,
% 8.11/1.40      (![X38, X37] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X38,k1_tarski(X37)),k1_xboole_0)) | (k1_tarski(X37) = k3_xboole_0(X38,k1_tarski(X37))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28503,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28502,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0)) | (k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28501,axiom,
% 8.11/1.40      (![X81, X80] : (((k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X80),X81),k1_xboole_0)) | (k1_xboole_0 = k3_xboole_0(X81,k1_tarski(X80))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28500,axiom,
% 8.11/1.40      (![X58, X59] : (((k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_tarski(X58),X59),k1_xboole_0)) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X58),X59)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28499,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X20),X21))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28498,axiom,
% 8.11/1.40      (![X32, X31] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X31),k4_xboole_0(k1_tarski(X31),X32))) | (k1_tarski(X31) = k3_xboole_0(X32,k1_tarski(X31))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28497,axiom,
% 8.11/1.40      (![X25, X24] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X24),k4_xboole_0(k1_tarski(X24),X25))) | (k1_tarski(X24) = k3_xboole_0(k1_tarski(X24),X25)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28496,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X20),k4_xboole_0(k1_tarski(X20),X21))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X20),X21)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28495,axiom,
% 8.11/1.40      (![X3, X2] : ((k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28494,axiom,
% 8.11/1.40      (![X5, X4] : ((k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28493,axiom,
% 8.11/1.40      (![X9, X10] : (((k1_tarski(X9) = k4_xboole_0(k1_tarski(X9),X10)) | (k1_tarski(X9) = k3_xboole_0(X10,k1_tarski(X9))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28492,axiom,
% 8.11/1.40      (![X15, X14] : (((k1_tarski(X14) = k4_xboole_0(k1_tarski(X14),X15)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X14),X15)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28491,axiom,
% 8.11/1.40      (![X1, X2] : (((k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)) | (k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28490,axiom,
% 8.11/1.40      (![X22, X23] : (((k1_tarski(X22) = k4_xboole_0(k1_tarski(X22),k3_xboole_0(k1_tarski(X22),X23))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X22),X23)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28489,axiom,
% 8.11/1.40      (![X56, X57] : (((k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),k3_xboole_0(k1_tarski(X56),X57))) | (k1_tarski(X56) = k3_xboole_0(k1_tarski(X56),X57)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28488,axiom,
% 8.11/1.40      (![X32, X31] : (((k1_tarski(X31) = k4_xboole_0(k1_tarski(X31),k3_xboole_0(k1_tarski(X31),X32))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X31),k3_xboole_0(X32,k1_tarski(X31)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28487,axiom,
% 8.11/1.40      (![X84, X85] : (((k1_tarski(X84) = k4_xboole_0(k1_tarski(X84),k3_xboole_0(k1_tarski(X84),X85))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X84))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X84),X85))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28486,axiom,
% 8.11/1.40      (![X16, X17] : (((k1_tarski(X16) = k4_xboole_0(k1_tarski(X16),k3_xboole_0(k1_tarski(X16),X17))) | (k1_xboole_0 = k1_tarski(X16)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X16),X17))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28485,axiom,
% 8.11/1.40      (![X98, X99] : (((k1_tarski(X98) = k4_xboole_0(k1_tarski(X98),k3_xboole_0(k1_tarski(X98),X99))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X98),X99))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28484,axiom,
% 8.11/1.40      (![X15, X14] : (((k1_tarski(X14) = k4_xboole_0(k1_tarski(X14),k3_xboole_0(k1_tarski(X14),X15))) | (k1_xboole_0 = k1_tarski(X14)) | (k1_tarski(X14) = k3_xboole_0(X15,k1_tarski(X14))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28483,axiom,
% 8.11/1.40      (![X115, X116] : (((k1_tarski(X115) = k4_xboole_0(k1_tarski(X115),k3_xboole_0(k1_tarski(X115),X116))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X115))) | (k1_tarski(X115) = k3_xboole_0(X116,k1_tarski(X115))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28482,axiom,
% 8.11/1.40      (![X148, X149] : (((k1_tarski(X148) = k4_xboole_0(k1_tarski(X148),k3_xboole_0(k1_tarski(X148),X149))) | (k1_tarski(X148) = k3_xboole_0(X149,k1_tarski(X148))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28481,axiom,
% 8.11/1.40      (![X75, X74] : (((k1_tarski(X74) = k4_xboole_0(k1_tarski(X74),k3_xboole_0(k1_tarski(X75),k1_tarski(X74)))) | (k1_xboole_0 = k1_tarski(X74)) | (k1_xboole_0 = k1_tarski(X75)) | (k1_tarski(X74) = k1_tarski(X75)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28480,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X51),k1_tarski(X52)))) | (k1_xboole_0 = k1_tarski(X52)) | (k1_tarski(X51) = k3_xboole_0(k1_tarski(X52),k1_tarski(X51))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28479,axiom,
% 8.11/1.40      (![X81, X80] : (((k1_tarski(X80) = k4_xboole_0(k1_tarski(X80),k3_xboole_0(k1_tarski(X81),k1_tarski(X80)))) | (k1_xboole_0 = k1_tarski(X80)) | (k1_tarski(X81) = k3_xboole_0(k1_tarski(X81),k1_tarski(X80))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28478,axiom,
% 8.11/1.40      (![X77, X76] : (((k1_tarski(X76) = k4_xboole_0(k1_tarski(X76),k3_xboole_0(k1_tarski(X77),k1_tarski(X76)))) | (k1_xboole_0 = k1_tarski(X76)) | (k1_tarski(X76) = k1_tarski(X77)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28477,axiom,
% 8.11/1.40      (![X53, X52] : (((k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X52),k1_tarski(X53)))) | (k1_xboole_0 = k1_tarski(X52)) | (k1_tarski(X53) = k3_xboole_0(k1_tarski(X53),k1_tarski(X52))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28476,axiom,
% 8.11/1.40      (![X84, X85] : (((k1_tarski(X85) = k4_xboole_0(k1_tarski(X85),k3_xboole_0(k1_tarski(X85),k1_tarski(X84)))) | (k1_xboole_0 = k1_tarski(X85)) | (k1_tarski(X84) = k3_xboole_0(k1_tarski(X85),k1_tarski(X84))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28475,axiom,
% 8.11/1.40      (![X11, X10] : (((k1_tarski(X11) = k4_xboole_0(k1_tarski(X11),k3_xboole_0(k1_tarski(X11),k1_tarski(X10)))) | (k1_xboole_0 = k1_tarski(X11)) | (k1_tarski(X11) = k1_tarski(X10)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28474,axiom,
% 8.11/1.40      (![X34, X35] : (((k1_tarski(X34) = k4_xboole_0(k1_tarski(X34),k3_xboole_0(X35,k1_tarski(X34)))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X34),X35)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28473,axiom,
% 8.11/1.40      (![X62, X61] : (((k1_tarski(X61) = k4_xboole_0(k1_tarski(X61),k3_xboole_0(X62,k1_tarski(X61)))) | (k1_tarski(X61) = k3_xboole_0(k1_tarski(X61),X62)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28472,axiom,
% 8.11/1.40      (![X63, X64] : (((k1_tarski(X63) = k4_xboole_0(k1_tarski(X63),k3_xboole_0(X64,k1_tarski(X63)))) | (k1_tarski(X63) = k3_xboole_0(X64,k1_tarski(X63))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28471,axiom,
% 8.11/1.40      (![X27, X28] : (((k1_xboole_0 = k4_xboole_0(k1_tarski(X27),k3_xboole_0(k1_tarski(X27),X28))) | (k1_tarski(X27) = k4_xboole_0(k1_tarski(X27),k3_xboole_0(X28,k1_tarski(X27)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28470,axiom,
% 8.11/1.40      (![X89, X88] : (((k1_tarski(X88) = k4_xboole_0(k1_tarski(X88),k3_xboole_0(X89,k1_tarski(X88)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X88))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X88),X89))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28469,axiom,
% 8.11/1.40      (![X18, X19] : (((k1_tarski(X18) = k4_xboole_0(k1_tarski(X18),k3_xboole_0(X19,k1_tarski(X18)))) | (k1_xboole_0 = k1_tarski(X18)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X18),X19))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28468,axiom,
% 8.11/1.40      (![X108, X107] : (((k1_tarski(X107) = k4_xboole_0(k1_tarski(X107),k3_xboole_0(X108,k1_tarski(X107)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X107),X108))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28467,axiom,
% 8.11/1.40      (![X81, X80] : (((k1_tarski(X80) = k4_xboole_0(k1_tarski(X80),k4_xboole_0(k1_tarski(X80),X81))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X80))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X80),X81))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28466,axiom,
% 8.11/1.40      (![X11, X10] : (((k1_tarski(X10) = k4_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X10),X11))) | (k1_xboole_0 = k1_tarski(X10)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X10),X11))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28465,axiom,
% 8.11/1.40      (![X96, X97] : (((k1_tarski(X96) = k4_xboole_0(k1_tarski(X96),k4_xboole_0(k1_tarski(X96),X97))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X96),X97))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28464,axiom,
% 8.11/1.40      (![X56, X57] : (((k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),k4_xboole_0(k1_tarski(X56),X57))) | (k1_tarski(X56) = k4_xboole_0(k1_tarski(X56),X57)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28463,axiom,
% 8.11/1.40      (![X53, X52] : (((k1_tarski(X52) = k4_xboole_0(k1_tarski(X52),k4_xboole_0(k1_tarski(X52),X53))) | (k1_xboole_0 = k3_xboole_0(X53,k1_tarski(X52))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28462,axiom,
% 8.11/1.40      (![X31, X30] : (((k1_tarski(X30) = k4_xboole_0(k1_tarski(X30),k4_xboole_0(k1_tarski(X30),X31))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X30),X31)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28461,axiom,
% 8.11/1.40      (![X22, X21] : (((k1_tarski(X21) = k4_xboole_0(k1_tarski(X21),k1_tarski(X22))) | (k1_tarski(X21) = k1_tarski(X22)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28460,axiom,
% 8.11/1.40      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28459,axiom,
% 8.11/1.40      (![X3, X2] : ((k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28458,axiom,
% 8.11/1.40      (![X7, X8] : (((k4_xboole_0(X7,k1_tarski(X8)) = k5_xboole_0(X7,k1_tarski(X8))) | (k1_xboole_0 = k3_xboole_0(X7,k1_tarski(X8))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28457,axiom,
% 8.11/1.40      (![X16, X15] : (((k4_xboole_0(X16,k1_tarski(X15)) = k5_xboole_0(X16,k1_tarski(X15))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X15),X16)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28456,axiom,
% 8.11/1.40      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28455,axiom,
% 8.11/1.40      (![X7, X6] : ((k3_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X6,X7)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28454,axiom,
% 8.11/1.40      (![X18, X17] : ((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X17,X18)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28453,axiom,
% 8.11/1.40      (![X62, X61] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X62),k1_tarski(X61)),k1_xboole_0)) | (k1_tarski(X61) = k1_tarski(X62)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28452,axiom,
% 8.11/1.40      (![X190, X189] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X189),X190),k1_xboole_0)) | (k1_tarski(X189) = k3_xboole_0(X190,k1_tarski(X189))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28451,axiom,
% 8.11/1.40      (![X139, X138] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X138),X139),k1_xboole_0)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X138),X139))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28450,axiom,
% 8.11/1.40      (![X53, X54] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X54),X53),k1_xboole_0)) | (k1_tarski(X54) = k3_xboole_0(k1_tarski(X54),X53)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28449,axiom,
% 8.11/1.40      (![X63, X62] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X62),X63),k1_xboole_0)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X62),X63)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28448,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X7),X8))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28447,axiom,
% 8.11/1.40      (![X102, X101] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X102,k1_tarski(X101)),k1_xboole_0)) | (k1_tarski(X101) = k3_xboole_0(k1_tarski(X101),X102)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28446,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X50,k1_tarski(X49)),k1_xboole_0)) | (k1_tarski(X49) = k3_xboole_0(X50,k1_tarski(X49))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28445,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28444,axiom,
% 8.11/1.40      (![X133, X132] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X133,k1_tarski(X132)),k1_tarski(X132))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X132),X133))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28443,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_tarski(X7))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28442,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X8,k1_tarski(X7)),k1_tarski(X7))) | (k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28441,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X52,k1_tarski(X51)),k1_tarski(X51))) | (k1_xboole_0 = k3_xboole_0(X52,k1_tarski(X51))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28440,axiom,
% 8.11/1.40      (![X48, X47] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X48,k1_tarski(X47)),k1_tarski(X47))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X47),X48)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28439,axiom,
% 8.11/1.40      (![X155, X156] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X155),X156),k1_tarski(X155))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X156,k1_tarski(X155)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28438,axiom,
% 8.11/1.40      (![X117, X118] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X117),X118),k1_tarski(X117))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X117),X118))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28437,axiom,
% 8.11/1.40      (![X89, X90] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X89),X90),k1_tarski(X89))) | (k1_tarski(X89) = k4_xboole_0(k1_tarski(X89),X90)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28436,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X50),X49),k1_tarski(X50))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X50),X49)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28435,axiom,
% 8.11/1.40      (![X48, X47] : (((k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_tarski(X48),X47),k1_tarski(X48))) | (k1_xboole_0 = k3_xboole_0(X47,k1_tarski(X48))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28434,axiom,
% 8.11/1.40      (![X65, X64] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X65),k1_tarski(X64)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X64))) | (k1_tarski(X65) = k3_xboole_0(k1_tarski(X64),k1_tarski(X65))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28433,axiom,
% 8.11/1.40      (![X63, X64] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X64),k1_tarski(X63)))) | (k1_tarski(X63) = k1_tarski(X64)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28432,axiom,
% 8.11/1.40      (![X1, X0] : (((k1_xboole_0 = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X0),X1))) | (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28431,axiom,
% 8.11/1.40      (![X1, X0] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X0),X1))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_tarski(X0))) | (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28430,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X12),X13))) | (k1_xboole_0 = k1_tarski(X12)) | (k1_tarski(X12) = k3_xboole_0(X13,k1_tarski(X12))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28429,axiom,
% 8.11/1.40      (![X29, X28] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X28),X29))) | (k1_tarski(X28) = k3_xboole_0(X29,k1_tarski(X28))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28428,axiom,
% 8.11/1.40      (![X55, X56] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X56),X55))) | (k1_tarski(X56) = k3_xboole_0(k1_tarski(X56),X55)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28427,axiom,
% 8.11/1.40      (![X65, X64] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X64),X65))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X64),X65)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28426,axiom,
% 8.11/1.40      (![X104, X103] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X104,k1_tarski(X103)))) | (k1_tarski(X103) = k3_xboole_0(k1_tarski(X103),X104)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28425,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X52,k1_tarski(X51)))) | (k1_tarski(X51) = k3_xboole_0(X52,k1_tarski(X51))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28424,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7)))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28423,axiom,
% 8.11/1.40      (![X58, X57] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X57),X58))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X58,k1_tarski(X57)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28422,axiom,
% 8.11/1.40      (![X141, X140] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X140),X141))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X140),X141))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28421,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X12),X13))) | (k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28420,axiom,
% 8.11/1.40      (![X95, X94] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X94),X95))) | (k1_xboole_0 = k3_xboole_0(X95,k1_tarski(X94))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28419,axiom,
% 8.11/1.40      (![X73, X72] : (((k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X72),X73))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X72),X73)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28418,axiom,
% 8.11/1.40      (![X137, X136] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X136),X137),k1_xboole_0)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X136),X137))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28417,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0)) | (k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28416,axiom,
% 8.11/1.40      (![X93, X92] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X92),X93),k1_xboole_0)) | (k1_xboole_0 = k3_xboole_0(X93,k1_tarski(X92))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28415,axiom,
% 8.11/1.40      (![X71, X70] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X70),X71),k1_xboole_0)) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X70),X71)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28414,axiom,
% 8.11/1.40      (![X60, X61] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X60),X61),k1_tarski(X60))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28413,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X41),X42),k1_tarski(X41))) | (k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28412,axiom,
% 8.11/1.40      (![X46, X47] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X46),X47),k1_tarski(X46))) | (k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28411,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_tarski(X12),X13),k1_tarski(X12))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28410,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X21),k1_tarski(X20))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X21),k1_tarski(X20))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28409,axiom,
% 8.11/1.40      (![X20, X21] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X20),k1_tarski(X21))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X21),k1_tarski(X20))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28408,axiom,
% 8.11/1.40      (![X166, X167] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X166),k3_xboole_0(X167,k1_tarski(X166)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X166),X167))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28407,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28406,axiom,
% 8.11/1.40      (![X7, X8] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7)))) | (k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28405,axiom,
% 8.11/1.40      (![X53, X54] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X53),k3_xboole_0(X54,k1_tarski(X53)))) | (k1_xboole_0 = k3_xboole_0(X54,k1_tarski(X53))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28404,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X49),k3_xboole_0(X50,k1_tarski(X49)))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X49),X50)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28403,axiom,
% 8.11/1.40      (![X197, X198] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X197),k3_xboole_0(k1_tarski(X197),X198))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X198,k1_tarski(X197)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28402,axiom,
% 8.11/1.40      (![X151, X152] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X151),k3_xboole_0(k1_tarski(X151),X152))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X151),X152))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28401,axiom,
% 8.11/1.40      (![X124, X123] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X123),k3_xboole_0(k1_tarski(X123),X124))) | (k1_tarski(X123) = k4_xboole_0(k1_tarski(X123),X124)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28400,axiom,
% 8.11/1.40      (![X51, X52] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X52),k3_xboole_0(k1_tarski(X52),X51))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X52),X51)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28399,axiom,
% 8.11/1.40      (![X49, X50] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X50),k3_xboole_0(k1_tarski(X50),X49))) | (k1_xboole_0 = k3_xboole_0(X49,k1_tarski(X50))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28398,axiom,
% 8.11/1.40      (![X60, X61] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X60),k4_xboole_0(k1_tarski(X60),X61))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28397,axiom,
% 8.11/1.40      (![X42, X41] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X41),k4_xboole_0(k1_tarski(X41),X42))) | (k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28396,axiom,
% 8.11/1.40      (![X46, X47] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X46),k4_xboole_0(k1_tarski(X46),X47))) | (k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28395,axiom,
% 8.11/1.40      (![X13, X12] : (((k1_xboole_0 = k5_xboole_0(k1_tarski(X12),k4_xboole_0(k1_tarski(X12),X13))) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28394,axiom,
% 8.11/1.40      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28393,axiom,
% 8.11/1.40      (![X0] : ((k2_tarski(X0,X0) = k1_tarski(X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28392,negated_conjecture,
% 8.11/1.40      ((~(k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))) | (~r2_hidden(sK0,sK1)) | (k1_xboole_0 = k1_tarski(sK0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28391,axiom,
% 8.11/1.40      (![X1, X0, X2] : ((k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28390,axiom,
% 8.11/1.40      (![X1, X3, X0, X2] : ((k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28389,axiom,
% 8.11/1.40      (![X1, X3, X0, X2, X4] : ((k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28388,axiom,
% 8.11/1.40      (![X1, X3, X5, X0, X2, X4] : ((k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28387,axiom,
% 8.11/1.40      (![X1, X3, X5, X0, X2, X4, X6] : ((k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28386,axiom,
% 8.11/1.40      v1_xboole_0(k1_xboole_0)).
% 8.11/1.40  
% 8.11/1.40  tff(u28385,axiom,
% 8.11/1.40      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28384,axiom,
% 8.11/1.40      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28383,axiom,
% 8.11/1.40      (![X0] : (r1_tarski(X0,X0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28382,axiom,
% 8.11/1.40      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28381,axiom,
% 8.11/1.40      (![X1] : (r1_tarski(k1_xboole_0,X1)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28380,axiom,
% 8.11/1.40      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28379,axiom,
% 8.11/1.40      (![X1, X2] : (r1_tarski(k3_xboole_0(X2,X1),X1)))).
% 8.11/1.40  
% 8.11/1.40  tff(u28378,axiom,
% 8.11/1.40      (![X1, X2] : ((r1_tarski(k1_tarski(X2),X1) | (k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X2))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28377,axiom,
% 8.11/1.40      (![X9, X10] : ((r1_tarski(k1_tarski(X9),X10) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X9),X10)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28376,axiom,
% 8.11/1.40      (![X1, X0] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28375,axiom,
% 8.11/1.40      (![X11, X12] : (r1_tarski(k3_xboole_0(X11,X12),k3_xboole_0(X12,X11))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28374,axiom,
% 8.11/1.40      (![X126, X127] : ((r1_tarski(k1_tarski(X126),k3_xboole_0(X127,k1_tarski(X126))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X126),X127))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28373,axiom,
% 8.11/1.40      (![X7, X8] : ((r1_tarski(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X8,k1_tarski(X7)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28372,axiom,
% 8.11/1.40      (![X7, X8] : ((r1_tarski(k1_tarski(X7),k3_xboole_0(X8,k1_tarski(X7))) | (k1_tarski(X7) = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28371,axiom,
% 8.11/1.40      (![X36, X35] : ((r1_tarski(k1_tarski(X35),k3_xboole_0(X36,k1_tarski(X35))) | (k1_xboole_0 = k3_xboole_0(X36,k1_tarski(X35))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28370,axiom,
% 8.11/1.40      (![X32, X31] : ((r1_tarski(k1_tarski(X31),k3_xboole_0(X32,k1_tarski(X31))) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X31),X32)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28369,axiom,
% 8.11/1.40      (![X150, X149] : ((r1_tarski(k1_tarski(X149),k3_xboole_0(k1_tarski(X149),X150)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X150,k1_tarski(X149)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28368,axiom,
% 8.11/1.40      (![X112, X111] : ((r1_tarski(k1_tarski(X111),k3_xboole_0(k1_tarski(X111),X112)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X111),X112))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28367,axiom,
% 8.11/1.40      (![X84, X83] : ((r1_tarski(k1_tarski(X83),k3_xboole_0(k1_tarski(X83),X84)) | (k1_tarski(X83) = k4_xboole_0(k1_tarski(X83),X84)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28366,axiom,
% 8.11/1.40      (![X34, X33] : ((r1_tarski(k1_tarski(X34),k3_xboole_0(k1_tarski(X34),X33)) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X34),X33)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28365,axiom,
% 8.11/1.40      (![X32, X31] : ((r1_tarski(k1_tarski(X32),k3_xboole_0(k1_tarski(X32),X31)) | (k1_xboole_0 = k3_xboole_0(X31,k1_tarski(X32))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28364,axiom,
% 8.11/1.40      (![X48, X47] : ((r1_tarski(k3_xboole_0(k1_tarski(X48),k1_tarski(X47)),k1_xboole_0) | (k1_tarski(X47) = k1_tarski(X48)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28363,axiom,
% 8.11/1.40      (![X7, X8] : ((r1_tarski(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X7),X8))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28362,axiom,
% 8.11/1.40      (![X87, X88] : ((r1_tarski(k3_xboole_0(X88,k1_tarski(X87)),k1_xboole_0) | (k1_tarski(X87) = k3_xboole_0(k1_tarski(X87),X88)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28361,axiom,
% 8.11/1.40      (![X7, X8] : ((r1_tarski(k3_xboole_0(X8,k1_tarski(X7)),k1_xboole_0) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X7),X8)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28360,axiom,
% 8.11/1.40      (![X36, X35] : ((r1_tarski(k3_xboole_0(X36,k1_tarski(X35)),k1_xboole_0) | (k1_tarski(X35) = k3_xboole_0(X36,k1_tarski(X35))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28359,axiom,
% 8.11/1.40      (![X176, X175] : ((r1_tarski(k3_xboole_0(k1_tarski(X175),X176),k1_xboole_0) | (k1_tarski(X175) = k3_xboole_0(X176,k1_tarski(X175))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28358,axiom,
% 8.11/1.40      (![X124, X125] : ((r1_tarski(k3_xboole_0(k1_tarski(X124),X125),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X124),X125))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28357,axiom,
% 8.11/1.40      (![X49, X48] : ((r1_tarski(k3_xboole_0(k1_tarski(X48),X49),k1_xboole_0) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X48),X49)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28356,axiom,
% 8.11/1.40      (![X40, X39] : ((r1_tarski(k3_xboole_0(k1_tarski(X40),X39),k1_xboole_0) | (k1_tarski(X40) = k3_xboole_0(k1_tarski(X40),X39)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28355,axiom,
% 8.11/1.40      (![X58, X57] : ((r1_tarski(k4_xboole_0(k1_tarski(X57),X58),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X58,k1_tarski(X57)))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28354,axiom,
% 8.11/1.40      (![X53, X52] : ((r1_tarski(k4_xboole_0(k1_tarski(X52),X53),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X52),X53))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28353,axiom,
% 8.11/1.40      (![X18, X17] : ((r1_tarski(k4_xboole_0(k1_tarski(X17),X18),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X18,k1_tarski(X17))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28352,axiom,
% 8.11/1.40      (![X20, X21] : ((r1_tarski(k4_xboole_0(k1_tarski(X20),X21),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k1_tarski(X20),X21)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28351,axiom,
% 8.11/1.40      (![X13, X12] : ((r1_tarski(k4_xboole_0(k1_tarski(X12),X13),k1_xboole_0) | (k1_tarski(X12) = k4_xboole_0(k1_tarski(X12),X13)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28350,axiom,
% 8.11/1.40      (![X65, X64] : ((r1_tarski(k1_tarski(X64),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X65),k1_tarski(X64)))) | (k1_tarski(X65) = k3_xboole_0(k1_tarski(X64),k1_tarski(X65))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28349,axiom,
% 8.11/1.40      (![X91, X90] : ((r1_tarski(k1_tarski(X90),k1_xboole_0) | (k1_tarski(X90) = k3_xboole_0(X91,k1_tarski(X90))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski(X90),X91))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28348,axiom,
% 8.11/1.40      (![X60, X61] : ((r1_tarski(k1_tarski(X60),k4_xboole_0(k1_tarski(X60),X61)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X60),X61))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28347,axiom,
% 8.11/1.40      (![X42, X41] : ((r1_tarski(k1_tarski(X41),k4_xboole_0(k1_tarski(X41),X42)) | (k1_tarski(X41) = k3_xboole_0(X42,k1_tarski(X41))))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28346,axiom,
% 8.11/1.40      (![X46, X47] : ((r1_tarski(k1_tarski(X46),k4_xboole_0(k1_tarski(X46),X47)) | (k1_tarski(X46) = k3_xboole_0(k1_tarski(X46),X47)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28345,axiom,
% 8.11/1.40      (![X18, X19] : ((r1_tarski(k1_tarski(X18),k4_xboole_0(k1_tarski(X18),X19)) | (k1_xboole_0 = k4_xboole_0(k1_tarski(X18),X19)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28344,axiom,
% 8.11/1.40      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28343,axiom,
% 8.11/1.40      (![X1, X0] : ((r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28342,axiom,
% 8.11/1.40      (![X1, X0] : ((r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) != X0))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28341,axiom,
% 8.11/1.40      (![X0] : ((~r2_hidden(X0,k1_xboole_0) | (k1_xboole_0 = k1_tarski(X0)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28340,axiom,
% 8.11/1.40      (![X7, X6] : ((~r2_hidden(X6,X7) | (k1_tarski(X6) = k3_xboole_0(k1_tarski(X6),X7)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28339,axiom,
% 8.11/1.40      (![X1, X0] : ((r2_hidden(X0,X1) | (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28338,axiom,
% 8.11/1.40      (![X1, X0] : ((r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))))).
% 8.11/1.40  
% 8.11/1.40  tff(u28337,negated_conjecture,
% 8.11/1.40      ((~r2_hidden(sK0,sK1)) | r2_hidden(sK0,sK1))).
% 8.11/1.40  
% 8.11/1.40  tff(u28336,negated_conjecture,
% 8.11/1.40      ((~(k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))) | (~r2_hidden(sK0,sK1)) | (![X1] : ((r2_hidden(sK0,X1) | r1_xboole_0(k1_xboole_0,X1)))))).
% 8.11/1.40  
% 8.11/1.40  % (3982)# SZS output end Saturation.
% 8.11/1.40  % (3982)------------------------------
% 8.11/1.40  % (3982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.11/1.40  % (3982)Termination reason: Satisfiable
% 8.11/1.40  
% 8.11/1.40  % (3982)Memory used [KB]: 12025
% 8.11/1.40  % (3982)Time elapsed: 0.975 s
% 8.11/1.40  % (3982)------------------------------
% 8.11/1.40  % (3982)------------------------------
% 8.11/1.40  % (3965)Success in time 1.046 s
%------------------------------------------------------------------------------
