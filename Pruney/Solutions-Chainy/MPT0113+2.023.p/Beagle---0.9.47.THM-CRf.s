%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 214 expanded)
%              Number of leaves         :   29 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 273 expanded)
%              Number of equality atoms :   87 ( 168 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_5945,plain,(
    ! [A_212,B_213] :
      ( r1_xboole_0(A_212,B_213)
      | k3_xboole_0(A_212,B_213) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_453,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | k4_xboole_0(A_69,B_70) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_461,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_453,c_59])).

tff(c_24,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_482,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_506,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_482])).

tff(c_512,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_506])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_41] : r1_tarski(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_18])).

tff(c_272,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_294,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(resolution,[status(thm)],[c_145,c_272])).

tff(c_28,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_41,B_42] : r1_xboole_0(k1_xboole_0,k2_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_28])).

tff(c_301,plain,(
    ! [A_62] : r1_xboole_0(k1_xboole_0,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_148])).

tff(c_513,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_xboole_0(A_75,C_76)
      | ~ r1_xboole_0(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_894,plain,(
    ! [A_91,A_92] :
      ( r1_xboole_0(A_91,A_92)
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_301,c_513])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1019,plain,(
    ! [A_97,A_98] :
      ( k4_xboole_0(A_97,A_98) = A_97
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_894,c_30])).

tff(c_1025,plain,(
    ! [A_5,A_98] :
      ( k4_xboole_0(A_5,A_98) = A_5
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1019])).

tff(c_1051,plain,(
    ! [A_98] : k4_xboole_0(k1_xboole_0,A_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_1025])).

tff(c_1162,plain,(
    ! [A_101,B_102,C_103] : k2_xboole_0(k4_xboole_0(A_101,B_102),k3_xboole_0(A_101,C_103)) = k4_xboole_0(A_101,k4_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1186,plain,(
    ! [A_11,C_103] : k4_xboole_0(A_11,k4_xboole_0(k1_xboole_0,C_103)) = k2_xboole_0(A_11,k3_xboole_0(A_11,C_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_1162])).

tff(c_1251,plain,(
    ! [A_108,C_109] : k2_xboole_0(A_108,k3_xboole_0(A_108,C_109)) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_1051,c_1186])).

tff(c_1289,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1251])).

tff(c_670,plain,(
    ! [A_83,B_84] : k5_xboole_0(k5_xboole_0(A_83,B_84),k2_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_700,plain,(
    ! [A_19] : k5_xboole_0(A_19,k2_xboole_0(A_19,k1_xboole_0)) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_670])).

tff(c_707,plain,(
    ! [A_19] : k5_xboole_0(A_19,k2_xboole_0(A_19,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_700])).

tff(c_1297,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_707])).

tff(c_1053,plain,(
    ! [A_99,A_100] :
      ( k4_xboole_0(A_99,A_100) = A_99
      | k1_xboole_0 != A_99 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_1025])).

tff(c_158,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_48,B_49] : k3_xboole_0(k4_xboole_0(A_48,B_49),B_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_173,plain,(
    ! [B_49,A_48] : k3_xboole_0(B_49,k4_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_2])).

tff(c_491,plain,(
    ! [B_49,A_48] : k4_xboole_0(B_49,k4_xboole_0(A_48,B_49)) = k5_xboole_0(B_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_482])).

tff(c_509,plain,(
    ! [B_49,A_48] : k4_xboole_0(B_49,k4_xboole_0(A_48,B_49)) = B_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_491])).

tff(c_1389,plain,(
    ! [A_112,A_113] :
      ( k4_xboole_0(A_112,A_113) = A_112
      | k1_xboole_0 != A_113 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_509])).

tff(c_362,plain,(
    ! [A_65,B_66] : k2_xboole_0(k4_xboole_0(A_65,B_66),A_65) = A_65 ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_368,plain,(
    ! [A_65,B_66] : k4_xboole_0(k4_xboole_0(A_65,B_66),A_65) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_20])).

tff(c_1806,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(A_122,B_123) = k1_xboole_0
      | k1_xboole_0 != A_122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_368])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_460,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(A_69,B_70) = B_70
      | k4_xboole_0(A_69,B_70) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_453,c_14])).

tff(c_1918,plain,(
    ! [A_122,B_123] :
      ( k2_xboole_0(A_122,B_123) = B_123
      | k1_xboole_0 != A_122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1806,c_460])).

tff(c_36,plain,(
    ! [A_30,B_31] : k5_xboole_0(k5_xboole_0(A_30,B_31),k2_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_906,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4257,plain,(
    ! [A_164,B_165] : k5_xboole_0(A_164,k5_xboole_0(B_165,k2_xboole_0(A_164,B_165))) = k3_xboole_0(A_164,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_906])).

tff(c_4307,plain,(
    ! [A_122,B_123] :
      ( k5_xboole_0(A_122,k5_xboole_0(B_123,B_123)) = k3_xboole_0(A_122,B_123)
      | k1_xboole_0 != A_122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1918,c_4257])).

tff(c_4591,plain,(
    ! [B_123] : k3_xboole_0(k1_xboole_0,B_123) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1297,c_4307])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_272])).

tff(c_356,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_20])).

tff(c_5095,plain,(
    ! [A_176,B_177,C_178] : k4_xboole_0(k4_xboole_0(A_176,B_177),k4_xboole_0(A_176,k4_xboole_0(B_177,C_178))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_20])).

tff(c_5312,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_5095])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_238,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_228])).

tff(c_5385,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_238])).

tff(c_5461,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_2,c_5385])).

tff(c_5463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_5461])).

tff(c_5464,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_5957,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5945,c_5464])).

tff(c_5810,plain,(
    ! [A_204,B_205] :
      ( k4_xboole_0(A_204,B_205) = k1_xboole_0
      | ~ r1_tarski(A_204,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5828,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_5810])).

tff(c_5569,plain,(
    ! [A_189,B_190] :
      ( k4_xboole_0(A_189,B_190) = A_189
      | ~ r1_xboole_0(A_189,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7712,plain,(
    ! [A_271,B_272] : k4_xboole_0(k4_xboole_0(A_271,B_272),B_272) = k4_xboole_0(A_271,B_272) ),
    inference(resolution,[status(thm)],[c_28,c_5569])).

tff(c_5549,plain,(
    ! [A_182,B_183] : k4_xboole_0(A_182,k2_xboole_0(A_182,B_183)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5554,plain,(
    ! [A_182] : r1_tarski(k1_xboole_0,A_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_5549,c_18])).

tff(c_5680,plain,(
    ! [A_199,B_200] :
      ( k2_xboole_0(A_199,B_200) = B_200
      | ~ r1_tarski(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5693,plain,(
    ! [A_182] : k2_xboole_0(k1_xboole_0,A_182) = A_182 ),
    inference(resolution,[status(thm)],[c_5554,c_5680])).

tff(c_6726,plain,(
    ! [A_246,B_247,C_248] : k2_xboole_0(k4_xboole_0(A_246,B_247),k3_xboole_0(A_246,C_248)) = k4_xboole_0(A_246,k4_xboole_0(B_247,C_248)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6759,plain,(
    ! [C_248] : k4_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_248)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_248)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5828,c_6726])).

tff(c_6786,plain,(
    ! [C_248] : k4_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_248)) = k3_xboole_0('#skF_1',C_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5693,c_6759])).

tff(c_7722,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_6786])).

tff(c_7820,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5828,c_7722])).

tff(c_7822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5957,c_7820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:42:40 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.00  
% 5.42/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.01  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.42/2.01  
% 5.42/2.01  %Foreground sorts:
% 5.42/2.01  
% 5.42/2.01  
% 5.42/2.01  %Background operators:
% 5.42/2.01  
% 5.42/2.01  
% 5.42/2.01  %Foreground operators:
% 5.42/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.42/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.42/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.42/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.42/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.42/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.42/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.42/2.01  
% 5.42/2.03  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.42/2.03  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.42/2.03  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.42/2.03  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.42/2.03  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.42/2.03  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.42/2.03  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.42/2.03  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.42/2.03  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.42/2.03  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.42/2.03  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.42/2.03  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.42/2.03  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.42/2.03  tff(f_67, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.42/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.42/2.03  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.42/2.03  tff(c_5945, plain, (![A_212, B_213]: (r1_xboole_0(A_212, B_213) | k3_xboole_0(A_212, B_213)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.03  tff(c_453, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | k4_xboole_0(A_69, B_70)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.42/2.03  tff(c_38, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.42/2.03  tff(c_59, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 5.42/2.03  tff(c_461, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_453, c_59])).
% 5.42/2.03  tff(c_24, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.42/2.03  tff(c_16, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.42/2.03  tff(c_482, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.42/2.03  tff(c_506, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_482])).
% 5.42/2.03  tff(c_512, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_506])).
% 5.42/2.03  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.42/2.03  tff(c_140, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(A_41, B_42))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.42/2.03  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.42/2.03  tff(c_145, plain, (![A_41]: (r1_tarski(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_140, c_18])).
% 5.42/2.03  tff(c_272, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.42/2.03  tff(c_294, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(resolution, [status(thm)], [c_145, c_272])).
% 5.42/2.03  tff(c_28, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.42/2.03  tff(c_148, plain, (![A_41, B_42]: (r1_xboole_0(k1_xboole_0, k2_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_28])).
% 5.42/2.03  tff(c_301, plain, (![A_62]: (r1_xboole_0(k1_xboole_0, A_62))), inference(superposition, [status(thm), theory('equality')], [c_294, c_148])).
% 5.42/2.03  tff(c_513, plain, (![A_75, C_76, B_77]: (r1_xboole_0(A_75, C_76) | ~r1_xboole_0(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.42/2.03  tff(c_894, plain, (![A_91, A_92]: (r1_xboole_0(A_91, A_92) | ~r1_tarski(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_301, c_513])).
% 5.42/2.03  tff(c_30, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.42/2.03  tff(c_1019, plain, (![A_97, A_98]: (k4_xboole_0(A_97, A_98)=A_97 | ~r1_tarski(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_894, c_30])).
% 5.42/2.03  tff(c_1025, plain, (![A_5, A_98]: (k4_xboole_0(A_5, A_98)=A_5 | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1019])).
% 5.42/2.03  tff(c_1051, plain, (![A_98]: (k4_xboole_0(k1_xboole_0, A_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_1025])).
% 5.42/2.03  tff(c_1162, plain, (![A_101, B_102, C_103]: (k2_xboole_0(k4_xboole_0(A_101, B_102), k3_xboole_0(A_101, C_103))=k4_xboole_0(A_101, k4_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.42/2.03  tff(c_1186, plain, (![A_11, C_103]: (k4_xboole_0(A_11, k4_xboole_0(k1_xboole_0, C_103))=k2_xboole_0(A_11, k3_xboole_0(A_11, C_103)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_1162])).
% 5.42/2.03  tff(c_1251, plain, (![A_108, C_109]: (k2_xboole_0(A_108, k3_xboole_0(A_108, C_109))=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_1051, c_1186])).
% 5.42/2.03  tff(c_1289, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1251])).
% 5.42/2.03  tff(c_670, plain, (![A_83, B_84]: (k5_xboole_0(k5_xboole_0(A_83, B_84), k2_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.03  tff(c_700, plain, (![A_19]: (k5_xboole_0(A_19, k2_xboole_0(A_19, k1_xboole_0))=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_670])).
% 5.42/2.03  tff(c_707, plain, (![A_19]: (k5_xboole_0(A_19, k2_xboole_0(A_19, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_700])).
% 5.42/2.03  tff(c_1297, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1289, c_707])).
% 5.42/2.03  tff(c_1053, plain, (![A_99, A_100]: (k4_xboole_0(A_99, A_100)=A_99 | k1_xboole_0!=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_1025])).
% 5.42/2.03  tff(c_158, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.03  tff(c_168, plain, (![A_48, B_49]: (k3_xboole_0(k4_xboole_0(A_48, B_49), B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_158])).
% 5.42/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.42/2.03  tff(c_173, plain, (![B_49, A_48]: (k3_xboole_0(B_49, k4_xboole_0(A_48, B_49))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_2])).
% 5.42/2.03  tff(c_491, plain, (![B_49, A_48]: (k4_xboole_0(B_49, k4_xboole_0(A_48, B_49))=k5_xboole_0(B_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_173, c_482])).
% 5.42/2.03  tff(c_509, plain, (![B_49, A_48]: (k4_xboole_0(B_49, k4_xboole_0(A_48, B_49))=B_49)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_491])).
% 5.42/2.03  tff(c_1389, plain, (![A_112, A_113]: (k4_xboole_0(A_112, A_113)=A_112 | k1_xboole_0!=A_113)), inference(superposition, [status(thm), theory('equality')], [c_1053, c_509])).
% 5.42/2.03  tff(c_362, plain, (![A_65, B_66]: (k2_xboole_0(k4_xboole_0(A_65, B_66), A_65)=A_65)), inference(resolution, [status(thm)], [c_18, c_272])).
% 5.42/2.03  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.42/2.03  tff(c_368, plain, (![A_65, B_66]: (k4_xboole_0(k4_xboole_0(A_65, B_66), A_65)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_362, c_20])).
% 5.42/2.03  tff(c_1806, plain, (![A_122, B_123]: (k4_xboole_0(A_122, B_123)=k1_xboole_0 | k1_xboole_0!=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1389, c_368])).
% 5.42/2.03  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.42/2.03  tff(c_460, plain, (![A_69, B_70]: (k2_xboole_0(A_69, B_70)=B_70 | k4_xboole_0(A_69, B_70)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_453, c_14])).
% 5.42/2.03  tff(c_1918, plain, (![A_122, B_123]: (k2_xboole_0(A_122, B_123)=B_123 | k1_xboole_0!=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1806, c_460])).
% 5.42/2.03  tff(c_36, plain, (![A_30, B_31]: (k5_xboole_0(k5_xboole_0(A_30, B_31), k2_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.03  tff(c_906, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.42/2.03  tff(c_4257, plain, (![A_164, B_165]: (k5_xboole_0(A_164, k5_xboole_0(B_165, k2_xboole_0(A_164, B_165)))=k3_xboole_0(A_164, B_165))), inference(superposition, [status(thm), theory('equality')], [c_36, c_906])).
% 5.42/2.03  tff(c_4307, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, B_123))=k3_xboole_0(A_122, B_123) | k1_xboole_0!=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1918, c_4257])).
% 5.42/2.03  tff(c_4591, plain, (![B_123]: (k3_xboole_0(k1_xboole_0, B_123)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1297, c_4307])).
% 5.42/2.03  tff(c_40, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.42/2.03  tff(c_284, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_272])).
% 5.42/2.03  tff(c_356, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_284, c_20])).
% 5.42/2.03  tff(c_5095, plain, (![A_176, B_177, C_178]: (k4_xboole_0(k4_xboole_0(A_176, B_177), k4_xboole_0(A_176, k4_xboole_0(B_177, C_178)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1162, c_20])).
% 5.42/2.03  tff(c_5312, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_356, c_5095])).
% 5.42/2.03  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.03  tff(c_228, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.42/2.03  tff(c_238, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_228])).
% 5.42/2.03  tff(c_5385, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5312, c_238])).
% 5.42/2.03  tff(c_5461, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4591, c_2, c_5385])).
% 5.42/2.03  tff(c_5463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_5461])).
% 5.42/2.03  tff(c_5464, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.42/2.03  tff(c_5957, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5945, c_5464])).
% 5.42/2.03  tff(c_5810, plain, (![A_204, B_205]: (k4_xboole_0(A_204, B_205)=k1_xboole_0 | ~r1_tarski(A_204, B_205))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.42/2.03  tff(c_5828, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_5810])).
% 5.42/2.03  tff(c_5569, plain, (![A_189, B_190]: (k4_xboole_0(A_189, B_190)=A_189 | ~r1_xboole_0(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.42/2.03  tff(c_7712, plain, (![A_271, B_272]: (k4_xboole_0(k4_xboole_0(A_271, B_272), B_272)=k4_xboole_0(A_271, B_272))), inference(resolution, [status(thm)], [c_28, c_5569])).
% 5.42/2.03  tff(c_5549, plain, (![A_182, B_183]: (k4_xboole_0(A_182, k2_xboole_0(A_182, B_183))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.42/2.03  tff(c_5554, plain, (![A_182]: (r1_tarski(k1_xboole_0, A_182))), inference(superposition, [status(thm), theory('equality')], [c_5549, c_18])).
% 5.42/2.03  tff(c_5680, plain, (![A_199, B_200]: (k2_xboole_0(A_199, B_200)=B_200 | ~r1_tarski(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.42/2.03  tff(c_5693, plain, (![A_182]: (k2_xboole_0(k1_xboole_0, A_182)=A_182)), inference(resolution, [status(thm)], [c_5554, c_5680])).
% 5.42/2.03  tff(c_6726, plain, (![A_246, B_247, C_248]: (k2_xboole_0(k4_xboole_0(A_246, B_247), k3_xboole_0(A_246, C_248))=k4_xboole_0(A_246, k4_xboole_0(B_247, C_248)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.42/2.03  tff(c_6759, plain, (![C_248]: (k4_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_248))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_248)))), inference(superposition, [status(thm), theory('equality')], [c_5828, c_6726])).
% 5.42/2.03  tff(c_6786, plain, (![C_248]: (k4_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_248))=k3_xboole_0('#skF_1', C_248))), inference(demodulation, [status(thm), theory('equality')], [c_5693, c_6759])).
% 5.42/2.03  tff(c_7722, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7712, c_6786])).
% 5.42/2.03  tff(c_7820, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5828, c_7722])).
% 5.42/2.03  tff(c_7822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5957, c_7820])).
% 5.42/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.03  
% 5.42/2.03  Inference rules
% 5.42/2.03  ----------------------
% 5.42/2.03  #Ref     : 0
% 5.42/2.03  #Sup     : 1957
% 5.42/2.03  #Fact    : 0
% 5.42/2.03  #Define  : 0
% 5.42/2.03  #Split   : 2
% 5.42/2.03  #Chain   : 0
% 5.42/2.03  #Close   : 0
% 5.42/2.03  
% 5.42/2.03  Ordering : KBO
% 5.42/2.03  
% 5.42/2.03  Simplification rules
% 5.42/2.03  ----------------------
% 5.42/2.03  #Subsume      : 290
% 5.42/2.03  #Demod        : 1130
% 5.42/2.03  #Tautology    : 1196
% 5.42/2.03  #SimpNegUnit  : 65
% 5.42/2.03  #BackRed      : 10
% 5.42/2.03  
% 5.42/2.03  #Partial instantiations: 0
% 5.42/2.03  #Strategies tried      : 1
% 5.42/2.03  
% 5.42/2.03  Timing (in seconds)
% 5.42/2.03  ----------------------
% 5.42/2.03  Preprocessing        : 0.29
% 5.42/2.03  Parsing              : 0.16
% 5.42/2.03  CNF conversion       : 0.02
% 5.42/2.03  Main loop            : 0.99
% 5.42/2.03  Inferencing          : 0.32
% 5.42/2.03  Reduction            : 0.41
% 5.42/2.03  Demodulation         : 0.31
% 5.42/2.03  BG Simplification    : 0.04
% 5.42/2.03  Subsumption          : 0.14
% 5.42/2.03  Abstraction          : 0.06
% 5.42/2.03  MUC search           : 0.00
% 5.42/2.03  Cooper               : 0.00
% 5.42/2.03  Total                : 1.32
% 5.42/2.03  Index Insertion      : 0.00
% 5.42/2.03  Index Deletion       : 0.00
% 5.42/2.03  Index Matching       : 0.00
% 5.42/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
