%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:17 EST 2020

% Result     : Theorem 13.35s
% Output     : CNFRefutation 13.35s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 275 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  139 ( 520 expanded)
%              Number of equality atoms :   58 ( 239 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A] :
      ( r2_hidden(k1_xboole_0,A)
     => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_80,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_86,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [E_20,B_15,C_16] : r2_hidden(E_20,k1_enumset1(E_20,B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_183,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_197,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_38])).

tff(c_34,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_220,plain,(
    ! [B_66,A_67] : r2_hidden(B_66,k2_tarski(A_67,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_34])).

tff(c_80,plain,(
    ! [A_36] :
      ( k1_setfam_1(A_36) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_258,plain,(
    ! [A_71] : k1_setfam_1(k2_tarski(A_71,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_220,c_80])).

tff(c_78,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k1_setfam_1(B_35),A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_418,plain,(
    ! [A_95,A_96] :
      ( r1_tarski(k1_xboole_0,A_95)
      | ~ r2_hidden(A_95,k2_tarski(A_96,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_78])).

tff(c_438,plain,(
    ! [A_62] : r1_tarski(k1_xboole_0,A_62) ),
    inference(resolution,[status(thm)],[c_197,c_418])).

tff(c_21828,plain,(
    ! [A_17995,B_17996,C_17997] :
      ( r2_hidden('#skF_2'(A_17995,B_17996,C_17997),A_17995)
      | r2_hidden('#skF_3'(A_17995,B_17996,C_17997),C_17997)
      | k4_xboole_0(A_17995,B_17996) = C_17997 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22521,plain,(
    ! [A_18816,B_18817] :
      ( r2_hidden('#skF_3'(A_18816,B_18817,A_18816),A_18816)
      | k4_xboole_0(A_18816,B_18817) = A_18816 ) ),
    inference(resolution,[status(thm)],[c_21828,c_20])).

tff(c_389,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_555,plain,(
    ! [A_116,B_117] :
      ( '#skF_1'(k1_tarski(A_116),B_117) = A_116
      | r1_tarski(k1_tarski(A_116),B_117) ) ),
    inference(resolution,[status(thm)],[c_389,c_56])).

tff(c_446,plain,(
    ! [A_97] : r1_tarski(k1_xboole_0,A_97) ),
    inference(resolution,[status(thm)],[c_197,c_418])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_449,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_446,c_26])).

tff(c_585,plain,(
    ! [A_120] :
      ( k1_tarski(A_120) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_120),k1_xboole_0) = A_120 ) ),
    inference(resolution,[status(thm)],[c_555,c_449])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1285,plain,(
    ! [A_1919] :
      ( ~ r2_hidden(A_1919,k1_xboole_0)
      | r1_tarski(k1_tarski(A_1919),k1_xboole_0)
      | k1_tarski(A_1919) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_4])).

tff(c_1353,plain,(
    ! [A_1919] :
      ( ~ r2_hidden(A_1919,k1_xboole_0)
      | k1_tarski(A_1919) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1285,c_449])).

tff(c_22620,plain,(
    ! [B_19039] :
      ( k1_tarski('#skF_3'(k1_xboole_0,B_19039,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_19039) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22521,c_1353])).

tff(c_474,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_495,plain,(
    ! [C_25,B_100] :
      ( r2_hidden(C_25,B_100)
      | ~ r1_tarski(k1_tarski(C_25),B_100) ) ),
    inference(resolution,[status(thm)],[c_58,c_474])).

tff(c_22649,plain,(
    ! [B_19039,B_100] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_19039,k1_xboole_0),B_100)
      | ~ r1_tarski(k1_xboole_0,B_100)
      | k4_xboole_0(k1_xboole_0,B_19039) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22620,c_495])).

tff(c_22714,plain,(
    ! [B_19039,B_100] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_19039,k1_xboole_0),B_100)
      | k4_xboole_0(k1_xboole_0,B_19039) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_22649])).

tff(c_23925,plain,(
    ! [B_22940,B_22941] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_22940,k1_xboole_0),B_22941)
      | k4_xboole_0(k1_xboole_0,B_22940) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_22649])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25236,plain,(
    ! [B_26872,B_26873] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_26872,k1_xboole_0),B_26873)
      | k4_xboole_0(k1_xboole_0,B_26872) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_23925,c_10])).

tff(c_26121,plain,(
    ! [B_30622] : k4_xboole_0(k1_xboole_0,B_30622) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22714,c_25236])).

tff(c_27180,plain,(
    ! [D_34409,B_34410] :
      ( ~ r2_hidden(D_34409,B_34410)
      | ~ r2_hidden(D_34409,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26121,c_10])).

tff(c_27234,plain,(
    ! [E_20] : ~ r2_hidden(E_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_27180])).

tff(c_74,plain,(
    ! [A_32] : k3_tarski(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1382,plain,(
    ! [A_1993,B_1994] :
      ( r2_hidden('#skF_8'(A_1993,B_1994),A_1993)
      | r1_tarski(B_1994,k1_setfam_1(A_1993))
      | k1_xboole_0 = A_1993 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_29403,plain,(
    ! [A_41073,B_41074] :
      ( '#skF_8'(k1_tarski(A_41073),B_41074) = A_41073
      | r1_tarski(B_41074,k1_setfam_1(k1_tarski(A_41073)))
      | k1_tarski(A_41073) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1382,c_56])).

tff(c_76,plain,(
    ! [A_33] : r1_tarski(k1_setfam_1(A_33),k3_tarski(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_340,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_357,plain,(
    ! [A_33] :
      ( k3_tarski(A_33) = k1_setfam_1(A_33)
      | ~ r1_tarski(k3_tarski(A_33),k1_setfam_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_76,c_340])).

tff(c_29417,plain,(
    ! [A_41073] :
      ( k3_tarski(k1_tarski(A_41073)) = k1_setfam_1(k1_tarski(A_41073))
      | '#skF_8'(k1_tarski(A_41073),k3_tarski(k1_tarski(A_41073))) = A_41073
      | k1_tarski(A_41073) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_29403,c_357])).

tff(c_42336,plain,(
    ! [A_62509] :
      ( k1_setfam_1(k1_tarski(A_62509)) = A_62509
      | '#skF_8'(k1_tarski(A_62509),A_62509) = A_62509
      | k1_tarski(A_62509) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_29417])).

tff(c_42666,plain,
    ( '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42336,c_86])).

tff(c_42677,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42666])).

tff(c_42746,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42677,c_58])).

tff(c_42804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27234,c_42746])).

tff(c_42806,plain,(
    k1_tarski('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42666])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42805,plain,(
    '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_42666])).

tff(c_82,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,'#skF_8'(A_37,B_38))
      | r1_tarski(B_38,k1_setfam_1(A_37))
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42820,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42805,c_82])).

tff(c_42870,plain,
    ( r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42820])).

tff(c_42871,plain,(
    r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42806,c_42870])).

tff(c_355,plain,(
    ! [B_35,A_34] :
      ( k1_setfam_1(B_35) = A_34
      | ~ r1_tarski(A_34,k1_setfam_1(B_35))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_78,c_340])).

tff(c_42884,plain,
    ( k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_42871,c_355])).

tff(c_42944,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42884])).

tff(c_42946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_42944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.35/4.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.35/4.62  
% 13.35/4.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.35/4.62  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 13.35/4.62  
% 13.35/4.62  %Foreground sorts:
% 13.35/4.62  
% 13.35/4.62  
% 13.35/4.62  %Background operators:
% 13.35/4.62  
% 13.35/4.62  
% 13.35/4.62  %Foreground operators:
% 13.35/4.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.35/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.35/4.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.35/4.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.35/4.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.35/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.35/4.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.35/4.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.35/4.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.35/4.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.35/4.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.35/4.62  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 13.35/4.62  tff('#skF_9', type, '#skF_9': $i).
% 13.35/4.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 13.35/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.35/4.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.35/4.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 13.35/4.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.35/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.35/4.62  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.35/4.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.35/4.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.35/4.62  
% 13.35/4.64  tff(f_100, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 13.35/4.64  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.35/4.64  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 13.35/4.64  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.35/4.64  tff(f_88, axiom, (![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 13.35/4.64  tff(f_84, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 13.35/4.64  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.35/4.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.35/4.64  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.35/4.64  tff(f_78, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 13.35/4.64  tff(f_97, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 13.35/4.64  tff(f_80, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 13.35/4.64  tff(c_86, plain, (k1_setfam_1(k1_tarski('#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.35/4.64  tff(c_58, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.35/4.64  tff(c_38, plain, (![E_20, B_15, C_16]: (r2_hidden(E_20, k1_enumset1(E_20, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.35/4.64  tff(c_183, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.35/4.64  tff(c_197, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_38])).
% 13.35/4.64  tff(c_34, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.35/4.64  tff(c_220, plain, (![B_66, A_67]: (r2_hidden(B_66, k2_tarski(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_34])).
% 13.35/4.64  tff(c_80, plain, (![A_36]: (k1_setfam_1(A_36)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.35/4.64  tff(c_258, plain, (![A_71]: (k1_setfam_1(k2_tarski(A_71, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_220, c_80])).
% 13.35/4.64  tff(c_78, plain, (![B_35, A_34]: (r1_tarski(k1_setfam_1(B_35), A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.35/4.64  tff(c_418, plain, (![A_95, A_96]: (r1_tarski(k1_xboole_0, A_95) | ~r2_hidden(A_95, k2_tarski(A_96, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_78])).
% 13.35/4.64  tff(c_438, plain, (![A_62]: (r1_tarski(k1_xboole_0, A_62))), inference(resolution, [status(thm)], [c_197, c_418])).
% 13.35/4.64  tff(c_21828, plain, (![A_17995, B_17996, C_17997]: (r2_hidden('#skF_2'(A_17995, B_17996, C_17997), A_17995) | r2_hidden('#skF_3'(A_17995, B_17996, C_17997), C_17997) | k4_xboole_0(A_17995, B_17996)=C_17997)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.35/4.64  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.35/4.64  tff(c_22521, plain, (![A_18816, B_18817]: (r2_hidden('#skF_3'(A_18816, B_18817, A_18816), A_18816) | k4_xboole_0(A_18816, B_18817)=A_18816)), inference(resolution, [status(thm)], [c_21828, c_20])).
% 13.35/4.64  tff(c_389, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.35/4.64  tff(c_56, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.35/4.64  tff(c_555, plain, (![A_116, B_117]: ('#skF_1'(k1_tarski(A_116), B_117)=A_116 | r1_tarski(k1_tarski(A_116), B_117))), inference(resolution, [status(thm)], [c_389, c_56])).
% 13.35/4.64  tff(c_446, plain, (![A_97]: (r1_tarski(k1_xboole_0, A_97))), inference(resolution, [status(thm)], [c_197, c_418])).
% 13.35/4.64  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.35/4.64  tff(c_449, plain, (![A_97]: (k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_446, c_26])).
% 13.35/4.64  tff(c_585, plain, (![A_120]: (k1_tarski(A_120)=k1_xboole_0 | '#skF_1'(k1_tarski(A_120), k1_xboole_0)=A_120)), inference(resolution, [status(thm)], [c_555, c_449])).
% 13.35/4.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.35/4.64  tff(c_1285, plain, (![A_1919]: (~r2_hidden(A_1919, k1_xboole_0) | r1_tarski(k1_tarski(A_1919), k1_xboole_0) | k1_tarski(A_1919)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_585, c_4])).
% 13.35/4.64  tff(c_1353, plain, (![A_1919]: (~r2_hidden(A_1919, k1_xboole_0) | k1_tarski(A_1919)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1285, c_449])).
% 13.35/4.64  tff(c_22620, plain, (![B_19039]: (k1_tarski('#skF_3'(k1_xboole_0, B_19039, k1_xboole_0))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_19039)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22521, c_1353])).
% 13.35/4.64  tff(c_474, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.35/4.64  tff(c_495, plain, (![C_25, B_100]: (r2_hidden(C_25, B_100) | ~r1_tarski(k1_tarski(C_25), B_100))), inference(resolution, [status(thm)], [c_58, c_474])).
% 13.35/4.64  tff(c_22649, plain, (![B_19039, B_100]: (r2_hidden('#skF_3'(k1_xboole_0, B_19039, k1_xboole_0), B_100) | ~r1_tarski(k1_xboole_0, B_100) | k4_xboole_0(k1_xboole_0, B_19039)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22620, c_495])).
% 13.35/4.64  tff(c_22714, plain, (![B_19039, B_100]: (r2_hidden('#skF_3'(k1_xboole_0, B_19039, k1_xboole_0), B_100) | k4_xboole_0(k1_xboole_0, B_19039)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_438, c_22649])).
% 13.35/4.64  tff(c_23925, plain, (![B_22940, B_22941]: (r2_hidden('#skF_3'(k1_xboole_0, B_22940, k1_xboole_0), B_22941) | k4_xboole_0(k1_xboole_0, B_22940)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_438, c_22649])).
% 13.35/4.64  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.35/4.64  tff(c_25236, plain, (![B_26872, B_26873]: (~r2_hidden('#skF_3'(k1_xboole_0, B_26872, k1_xboole_0), B_26873) | k4_xboole_0(k1_xboole_0, B_26872)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23925, c_10])).
% 13.35/4.64  tff(c_26121, plain, (![B_30622]: (k4_xboole_0(k1_xboole_0, B_30622)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22714, c_25236])).
% 13.35/4.64  tff(c_27180, plain, (![D_34409, B_34410]: (~r2_hidden(D_34409, B_34410) | ~r2_hidden(D_34409, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26121, c_10])).
% 13.35/4.64  tff(c_27234, plain, (![E_20]: (~r2_hidden(E_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_27180])).
% 13.35/4.64  tff(c_74, plain, (![A_32]: (k3_tarski(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.35/4.64  tff(c_1382, plain, (![A_1993, B_1994]: (r2_hidden('#skF_8'(A_1993, B_1994), A_1993) | r1_tarski(B_1994, k1_setfam_1(A_1993)) | k1_xboole_0=A_1993)), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.35/4.64  tff(c_29403, plain, (![A_41073, B_41074]: ('#skF_8'(k1_tarski(A_41073), B_41074)=A_41073 | r1_tarski(B_41074, k1_setfam_1(k1_tarski(A_41073))) | k1_tarski(A_41073)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1382, c_56])).
% 13.35/4.64  tff(c_76, plain, (![A_33]: (r1_tarski(k1_setfam_1(A_33), k3_tarski(A_33)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.35/4.64  tff(c_340, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.35/4.64  tff(c_357, plain, (![A_33]: (k3_tarski(A_33)=k1_setfam_1(A_33) | ~r1_tarski(k3_tarski(A_33), k1_setfam_1(A_33)))), inference(resolution, [status(thm)], [c_76, c_340])).
% 13.35/4.64  tff(c_29417, plain, (![A_41073]: (k3_tarski(k1_tarski(A_41073))=k1_setfam_1(k1_tarski(A_41073)) | '#skF_8'(k1_tarski(A_41073), k3_tarski(k1_tarski(A_41073)))=A_41073 | k1_tarski(A_41073)=k1_xboole_0)), inference(resolution, [status(thm)], [c_29403, c_357])).
% 13.35/4.64  tff(c_42336, plain, (![A_62509]: (k1_setfam_1(k1_tarski(A_62509))=A_62509 | '#skF_8'(k1_tarski(A_62509), A_62509)=A_62509 | k1_tarski(A_62509)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_29417])).
% 13.35/4.64  tff(c_42666, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9' | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42336, c_86])).
% 13.35/4.64  tff(c_42677, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42666])).
% 13.35/4.64  tff(c_42746, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42677, c_58])).
% 13.35/4.64  tff(c_42804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27234, c_42746])).
% 13.35/4.64  tff(c_42806, plain, (k1_tarski('#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42666])).
% 13.35/4.64  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.35/4.64  tff(c_42805, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_42666])).
% 13.35/4.64  tff(c_82, plain, (![B_38, A_37]: (~r1_tarski(B_38, '#skF_8'(A_37, B_38)) | r1_tarski(B_38, k1_setfam_1(A_37)) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.35/4.64  tff(c_42820, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42805, c_82])).
% 13.35/4.64  tff(c_42870, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42820])).
% 13.35/4.64  tff(c_42871, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_42806, c_42870])).
% 13.35/4.64  tff(c_355, plain, (![B_35, A_34]: (k1_setfam_1(B_35)=A_34 | ~r1_tarski(A_34, k1_setfam_1(B_35)) | ~r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_78, c_340])).
% 13.35/4.64  tff(c_42884, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9' | ~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_42871, c_355])).
% 13.35/4.64  tff(c_42944, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_42884])).
% 13.35/4.64  tff(c_42946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_42944])).
% 13.35/4.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.35/4.64  
% 13.35/4.64  Inference rules
% 13.35/4.64  ----------------------
% 13.35/4.64  #Ref     : 0
% 13.35/4.64  #Sup     : 6960
% 13.35/4.64  #Fact    : 28
% 13.35/4.64  #Define  : 0
% 13.35/4.64  #Split   : 6
% 13.35/4.64  #Chain   : 0
% 13.35/4.64  #Close   : 0
% 13.35/4.64  
% 13.35/4.64  Ordering : KBO
% 13.35/4.64  
% 13.35/4.64  Simplification rules
% 13.35/4.64  ----------------------
% 13.35/4.64  #Subsume      : 2278
% 13.35/4.64  #Demod        : 2486
% 13.35/4.64  #Tautology    : 1211
% 13.35/4.64  #SimpNegUnit  : 65
% 13.35/4.64  #BackRed      : 4
% 13.35/4.64  
% 13.35/4.64  #Partial instantiations: 28635
% 13.35/4.64  #Strategies tried      : 1
% 13.35/4.64  
% 13.35/4.64  Timing (in seconds)
% 13.35/4.64  ----------------------
% 13.35/4.64  Preprocessing        : 0.34
% 13.35/4.64  Parsing              : 0.17
% 13.35/4.64  CNF conversion       : 0.03
% 13.35/4.64  Main loop            : 3.51
% 13.35/4.64  Inferencing          : 1.50
% 13.35/4.64  Reduction            : 0.87
% 13.35/4.64  Demodulation         : 0.62
% 13.35/4.64  BG Simplification    : 0.13
% 13.35/4.64  Subsumption          : 0.74
% 13.35/4.64  Abstraction          : 0.20
% 13.35/4.64  MUC search           : 0.00
% 13.35/4.64  Cooper               : 0.00
% 13.35/4.64  Total                : 3.88
% 13.35/4.64  Index Insertion      : 0.00
% 13.35/4.64  Index Deletion       : 0.00
% 13.35/4.64  Index Matching       : 0.00
% 13.35/4.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
