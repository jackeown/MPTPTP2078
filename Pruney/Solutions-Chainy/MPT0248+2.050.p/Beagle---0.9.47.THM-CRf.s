%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 455 expanded)
%              Number of leaves         :   37 ( 160 expanded)
%              Depth                    :   16
%              Number of atoms          :  154 ( 740 expanded)
%              Number of equality atoms :  122 ( 680 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_54,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_95,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_111,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_111])).

tff(c_1025,plain,(
    ! [B_127,A_128] :
      ( k1_tarski(B_127) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k1_tarski(B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1038,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_114,c_1025])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_95,c_1038])).

tff(c_1052,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1571,plain,(
    ! [A_173,B_174] : k5_xboole_0(A_173,k3_xboole_0(A_173,B_174)) = k4_xboole_0(A_173,B_174) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2352,plain,(
    ! [A_209,B_210] : k5_xboole_0(A_209,k3_xboole_0(B_210,A_209)) = k4_xboole_0(A_209,B_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1571])).

tff(c_1130,plain,(
    ! [B_136,A_137] : k5_xboole_0(B_136,A_137) = k5_xboole_0(A_137,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1053,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1054,plain,(
    ! [A_20] : k5_xboole_0(A_20,'#skF_2') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_22])).

tff(c_1146,plain,(
    ! [A_137] : k5_xboole_0('#skF_2',A_137) = A_137 ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_1054])).

tff(c_2573,plain,(
    ! [B_216] : k4_xboole_0('#skF_2',B_216) = k3_xboole_0(B_216,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_1146])).

tff(c_48,plain,(
    ! [B_56] : r1_tarski(k1_xboole_0,k1_tarski(B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1056,plain,(
    ! [B_56] : r1_tarski('#skF_2',k1_tarski(B_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_48])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1420,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(A_158,B_159) = '#skF_2'
      | ~ r1_tarski(A_158,B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_10])).

tff(c_1451,plain,(
    ! [B_56] : k4_xboole_0('#skF_2',k1_tarski(B_56)) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1056,c_1420])).

tff(c_2600,plain,(
    ! [B_56] : k3_xboole_0(k1_tarski(B_56),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2573,c_1451])).

tff(c_1333,plain,(
    ! [A_153,B_154,C_155] : r1_tarski(k3_xboole_0(A_153,B_154),k2_xboole_0(A_153,C_155)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1357,plain,(
    ! [B_154] : r1_tarski(k3_xboole_0('#skF_2',B_154),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1333])).

tff(c_44,plain,(
    ! [B_56,A_55] :
      ( k1_tarski(B_56) = A_55
      | k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_tarski(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1953,plain,(
    ! [B_195,A_196] :
      ( k1_tarski(B_195) = A_196
      | A_196 = '#skF_2'
      | ~ r1_tarski(A_196,k1_tarski(B_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_44])).

tff(c_1971,plain,(
    ! [B_154] :
      ( k3_xboole_0('#skF_2',B_154) = k1_tarski('#skF_1')
      | k3_xboole_0('#skF_2',B_154) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_1357,c_1953])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1055,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_28])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1226,plain,(
    ! [A_139,B_140] : k3_tarski(k2_tarski(A_139,B_140)) = k2_xboole_0(A_139,B_140) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1235,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = k2_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1226])).

tff(c_2217,plain,(
    ! [A_204,B_205] : k4_xboole_0(k2_xboole_0(A_204,B_205),k3_xboole_0(A_204,B_205)) = k5_xboole_0(A_204,B_205) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2247,plain,(
    ! [A_27] : k4_xboole_0(k3_tarski(k1_tarski(A_27)),k3_xboole_0(A_27,A_27)) = k5_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_2217])).

tff(c_2267,plain,(
    ! [A_27] : k4_xboole_0(k3_tarski(k1_tarski(A_27)),A_27) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_6,c_2247])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1275,plain,(
    ! [A_147,B_148] :
      ( k3_xboole_0(A_147,B_148) = A_147
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1304,plain,(
    ! [A_150,B_151] : k3_xboole_0(A_150,k2_xboole_0(A_150,B_151)) = A_150 ),
    inference(resolution,[status(thm)],[c_24,c_1275])).

tff(c_1313,plain,(
    ! [A_27] : k3_xboole_0(A_27,k3_tarski(k1_tarski(A_27))) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_1304])).

tff(c_2385,plain,(
    ! [A_27] : k5_xboole_0(k3_tarski(k1_tarski(A_27)),A_27) = k4_xboole_0(k3_tarski(k1_tarski(A_27)),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_2352])).

tff(c_2843,plain,(
    ! [A_227] : k5_xboole_0(k3_tarski(k1_tarski(A_227)),A_227) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2385])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2416,plain,(
    ! [A_211,B_212,C_213] : k5_xboole_0(k5_xboole_0(A_211,B_212),C_213) = k5_xboole_0(A_211,k5_xboole_0(B_212,C_213)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2484,plain,(
    ! [A_26,C_213] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_213)) = k5_xboole_0('#skF_2',C_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_2416])).

tff(c_2505,plain,(
    ! [A_214,C_215] : k5_xboole_0(A_214,k5_xboole_0(A_214,C_215)) = C_215 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_2484])).

tff(c_2554,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2505])).

tff(c_2848,plain,(
    ! [A_227] : k3_tarski(k1_tarski(A_227)) = k5_xboole_0(A_227,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_2554])).

tff(c_2883,plain,(
    ! [A_227] : k3_tarski(k1_tarski(A_227)) = A_227 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_2848])).

tff(c_1348,plain,(
    ! [A_27,B_154] : r1_tarski(k3_xboole_0(A_27,B_154),k3_tarski(k1_tarski(A_27))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_1333])).

tff(c_3139,plain,(
    ! [A_239,B_240] : r1_tarski(k3_xboole_0(A_239,B_240),A_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2883,c_1348])).

tff(c_3158,plain,(
    ! [B_154] :
      ( r1_tarski(k1_tarski('#skF_1'),'#skF_2')
      | k3_xboole_0('#skF_2',B_154) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_3139])).

tff(c_3509,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3158])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3515,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_3509,c_16])).

tff(c_3518,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2600,c_3515])).

tff(c_3520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_3518])).

tff(c_3521,plain,(
    ! [B_154] : k3_xboole_0('#skF_2',B_154) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3158])).

tff(c_1578,plain,(
    ! [B_174] : k4_xboole_0('#skF_2',B_174) = k3_xboole_0('#skF_2',B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_1146])).

tff(c_3529,plain,(
    ! [B_174] : k4_xboole_0('#skF_2',B_174) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3521,c_1578])).

tff(c_2363,plain,(
    ! [B_210] : k4_xboole_0('#skF_2',B_210) = k3_xboole_0(B_210,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_1146])).

tff(c_3638,plain,(
    ! [B_210] : k3_xboole_0(B_210,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3529,c_2363])).

tff(c_2256,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2217])).

tff(c_2268,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_4,c_2,c_2256])).

tff(c_3676,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_2268])).

tff(c_1294,plain,(
    ! [B_56] : k3_xboole_0('#skF_2',k1_tarski(B_56)) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1056,c_1275])).

tff(c_2391,plain,(
    ! [B_56] : k5_xboole_0(k1_tarski(B_56),'#skF_2') = k4_xboole_0(k1_tarski(B_56),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_2352])).

tff(c_2412,plain,(
    ! [B_56] : k4_xboole_0(k1_tarski(B_56),'#skF_2') = k1_tarski(B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_2391])).

tff(c_3759,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3676,c_2412])).

tff(c_3766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1052,c_3759])).

tff(c_3767,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3768,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3935,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_3768,c_56])).

tff(c_3839,plain,(
    ! [B_270,A_271] : k5_xboole_0(B_270,A_271) = k5_xboole_0(A_271,B_270) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3855,plain,(
    ! [A_271] : k5_xboole_0(k1_xboole_0,A_271) = A_271 ),
    inference(superposition,[status(thm),theory(equality)],[c_3839,c_22])).

tff(c_5452,plain,(
    ! [A_350,B_351,C_352] : k5_xboole_0(k5_xboole_0(A_350,B_351),C_352) = k5_xboole_0(A_350,k5_xboole_0(B_351,C_352)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5516,plain,(
    ! [A_26,C_352] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_352)) = k5_xboole_0(k1_xboole_0,C_352) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5452])).

tff(c_5530,plain,(
    ! [A_353,C_354] : k5_xboole_0(A_353,k5_xboole_0(A_353,C_354)) = C_354 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_5516])).

tff(c_5573,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5530])).

tff(c_3796,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_58])).

tff(c_5339,plain,(
    ! [A_347,B_348] : k4_xboole_0(k2_xboole_0(A_347,B_348),k3_xboole_0(A_347,B_348)) = k5_xboole_0(A_347,B_348) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5390,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_5339])).

tff(c_5404,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_5390])).

tff(c_4441,plain,(
    ! [A_303,B_304] : k5_xboole_0(A_303,k3_xboole_0(A_303,B_304)) = k4_xboole_0(A_303,B_304) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6433,plain,(
    ! [A_385,B_386] : k5_xboole_0(A_385,k3_xboole_0(B_386,A_385)) = k4_xboole_0(A_385,B_386) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4441])).

tff(c_5529,plain,(
    ! [A_26,C_352] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_352)) = C_352 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_5516])).

tff(c_9758,plain,(
    ! [A_446,B_447] : k5_xboole_0(A_446,k4_xboole_0(A_446,B_447)) = k3_xboole_0(B_447,A_446) ),
    inference(superposition,[status(thm),theory(equality)],[c_6433,c_5529])).

tff(c_9841,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5404,c_9758])).

tff(c_9893,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5573,c_2,c_9841])).

tff(c_4012,plain,(
    ! [A_281,B_282,C_283] : r1_tarski(k3_xboole_0(A_281,B_282),k2_xboole_0(A_281,C_283)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4024,plain,(
    ! [B_282] : r1_tarski(k3_xboole_0('#skF_2',B_282),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_4012])).

tff(c_4869,plain,(
    ! [B_322,A_323] :
      ( k1_tarski(B_322) = A_323
      | k1_xboole_0 = A_323
      | ~ r1_tarski(A_323,k1_tarski(B_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4879,plain,(
    ! [A_323] :
      ( k1_tarski('#skF_1') = A_323
      | k1_xboole_0 = A_323
      | ~ r1_tarski(A_323,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3768,c_4869])).

tff(c_4911,plain,(
    ! [A_325] :
      ( A_325 = '#skF_2'
      | k1_xboole_0 = A_325
      | ~ r1_tarski(A_325,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_4879])).

tff(c_4930,plain,(
    ! [B_282] :
      ( k3_xboole_0('#skF_2',B_282) = '#skF_2'
      | k3_xboole_0('#skF_2',B_282) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4024,c_4911])).

tff(c_9941,plain,
    ( k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9893,c_4930])).

tff(c_9966,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9893,c_9941])).

tff(c_9968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3767,c_3935,c_9966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.52/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.52/2.50  
% 6.52/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.52/2.50  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.52/2.50  
% 6.52/2.50  %Foreground sorts:
% 6.52/2.50  
% 6.52/2.50  
% 6.52/2.50  %Background operators:
% 6.52/2.50  
% 6.52/2.50  
% 6.52/2.50  %Foreground operators:
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.52/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.52/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.52/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.52/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.52/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.52/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.52/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.52/2.50  tff('#skF_1', type, '#skF_1': $i).
% 6.52/2.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.52/2.50  
% 6.85/2.52  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.85/2.52  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.85/2.52  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.85/2.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.85/2.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.85/2.52  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.85/2.52  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.85/2.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.85/2.52  tff(f_45, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 6.85/2.52  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.85/2.52  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.85/2.52  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.85/2.52  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.85/2.52  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 6.85/2.52  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.85/2.52  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.85/2.52  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.85/2.52  tff(c_106, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 6.85/2.52  tff(c_52, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.85/2.52  tff(c_95, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 6.85/2.52  tff(c_58, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.85/2.52  tff(c_111, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.85/2.52  tff(c_114, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_111])).
% 6.85/2.52  tff(c_1025, plain, (![B_127, A_128]: (k1_tarski(B_127)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k1_tarski(B_127)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.85/2.52  tff(c_1038, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_114, c_1025])).
% 6.85/2.52  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_95, c_1038])).
% 6.85/2.52  tff(c_1052, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 6.85/2.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.85/2.52  tff(c_1571, plain, (![A_173, B_174]: (k5_xboole_0(A_173, k3_xboole_0(A_173, B_174))=k4_xboole_0(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.85/2.52  tff(c_2352, plain, (![A_209, B_210]: (k5_xboole_0(A_209, k3_xboole_0(B_210, A_209))=k4_xboole_0(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1571])).
% 6.85/2.52  tff(c_1130, plain, (![B_136, A_137]: (k5_xboole_0(B_136, A_137)=k5_xboole_0(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.85/2.52  tff(c_1053, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 6.85/2.52  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.85/2.52  tff(c_1054, plain, (![A_20]: (k5_xboole_0(A_20, '#skF_2')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_22])).
% 6.85/2.52  tff(c_1146, plain, (![A_137]: (k5_xboole_0('#skF_2', A_137)=A_137)), inference(superposition, [status(thm), theory('equality')], [c_1130, c_1054])).
% 6.85/2.52  tff(c_2573, plain, (![B_216]: (k4_xboole_0('#skF_2', B_216)=k3_xboole_0(B_216, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2352, c_1146])).
% 6.85/2.52  tff(c_48, plain, (![B_56]: (r1_tarski(k1_xboole_0, k1_tarski(B_56)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.85/2.52  tff(c_1056, plain, (![B_56]: (r1_tarski('#skF_2', k1_tarski(B_56)))), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_48])).
% 6.85/2.52  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.85/2.52  tff(c_1420, plain, (![A_158, B_159]: (k4_xboole_0(A_158, B_159)='#skF_2' | ~r1_tarski(A_158, B_159))), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_10])).
% 6.85/2.52  tff(c_1451, plain, (![B_56]: (k4_xboole_0('#skF_2', k1_tarski(B_56))='#skF_2')), inference(resolution, [status(thm)], [c_1056, c_1420])).
% 6.85/2.52  tff(c_2600, plain, (![B_56]: (k3_xboole_0(k1_tarski(B_56), '#skF_2')='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2573, c_1451])).
% 6.85/2.52  tff(c_1333, plain, (![A_153, B_154, C_155]: (r1_tarski(k3_xboole_0(A_153, B_154), k2_xboole_0(A_153, C_155)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.85/2.52  tff(c_1357, plain, (![B_154]: (r1_tarski(k3_xboole_0('#skF_2', B_154), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1333])).
% 6.85/2.52  tff(c_44, plain, (![B_56, A_55]: (k1_tarski(B_56)=A_55 | k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_tarski(B_56)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.85/2.52  tff(c_1953, plain, (![B_195, A_196]: (k1_tarski(B_195)=A_196 | A_196='#skF_2' | ~r1_tarski(A_196, k1_tarski(B_195)))), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_44])).
% 6.85/2.52  tff(c_1971, plain, (![B_154]: (k3_xboole_0('#skF_2', B_154)=k1_tarski('#skF_1') | k3_xboole_0('#skF_2', B_154)='#skF_2')), inference(resolution, [status(thm)], [c_1357, c_1953])).
% 6.85/2.52  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.85/2.52  tff(c_1055, plain, (![A_26]: (k5_xboole_0(A_26, A_26)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_28])).
% 6.85/2.52  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.85/2.52  tff(c_30, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.85/2.52  tff(c_1226, plain, (![A_139, B_140]: (k3_tarski(k2_tarski(A_139, B_140))=k2_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.85/2.52  tff(c_1235, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=k2_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1226])).
% 6.85/2.52  tff(c_2217, plain, (![A_204, B_205]: (k4_xboole_0(k2_xboole_0(A_204, B_205), k3_xboole_0(A_204, B_205))=k5_xboole_0(A_204, B_205))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.85/2.52  tff(c_2247, plain, (![A_27]: (k4_xboole_0(k3_tarski(k1_tarski(A_27)), k3_xboole_0(A_27, A_27))=k5_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_2217])).
% 6.85/2.52  tff(c_2267, plain, (![A_27]: (k4_xboole_0(k3_tarski(k1_tarski(A_27)), A_27)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_6, c_2247])).
% 6.85/2.52  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.85/2.52  tff(c_1275, plain, (![A_147, B_148]: (k3_xboole_0(A_147, B_148)=A_147 | ~r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.85/2.52  tff(c_1304, plain, (![A_150, B_151]: (k3_xboole_0(A_150, k2_xboole_0(A_150, B_151))=A_150)), inference(resolution, [status(thm)], [c_24, c_1275])).
% 6.85/2.52  tff(c_1313, plain, (![A_27]: (k3_xboole_0(A_27, k3_tarski(k1_tarski(A_27)))=A_27)), inference(superposition, [status(thm), theory('equality')], [c_1235, c_1304])).
% 6.85/2.52  tff(c_2385, plain, (![A_27]: (k5_xboole_0(k3_tarski(k1_tarski(A_27)), A_27)=k4_xboole_0(k3_tarski(k1_tarski(A_27)), A_27))), inference(superposition, [status(thm), theory('equality')], [c_1313, c_2352])).
% 6.85/2.52  tff(c_2843, plain, (![A_227]: (k5_xboole_0(k3_tarski(k1_tarski(A_227)), A_227)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2385])).
% 6.85/2.52  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.85/2.52  tff(c_2416, plain, (![A_211, B_212, C_213]: (k5_xboole_0(k5_xboole_0(A_211, B_212), C_213)=k5_xboole_0(A_211, k5_xboole_0(B_212, C_213)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.85/2.52  tff(c_2484, plain, (![A_26, C_213]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_213))=k5_xboole_0('#skF_2', C_213))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_2416])).
% 6.85/2.52  tff(c_2505, plain, (![A_214, C_215]: (k5_xboole_0(A_214, k5_xboole_0(A_214, C_215))=C_215)), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_2484])).
% 6.85/2.52  tff(c_2554, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2505])).
% 6.85/2.52  tff(c_2848, plain, (![A_227]: (k3_tarski(k1_tarski(A_227))=k5_xboole_0(A_227, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_2554])).
% 6.85/2.52  tff(c_2883, plain, (![A_227]: (k3_tarski(k1_tarski(A_227))=A_227)), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_2848])).
% 6.85/2.52  tff(c_1348, plain, (![A_27, B_154]: (r1_tarski(k3_xboole_0(A_27, B_154), k3_tarski(k1_tarski(A_27))))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_1333])).
% 6.85/2.52  tff(c_3139, plain, (![A_239, B_240]: (r1_tarski(k3_xboole_0(A_239, B_240), A_239))), inference(demodulation, [status(thm), theory('equality')], [c_2883, c_1348])).
% 6.85/2.52  tff(c_3158, plain, (![B_154]: (r1_tarski(k1_tarski('#skF_1'), '#skF_2') | k3_xboole_0('#skF_2', B_154)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1971, c_3139])).
% 6.85/2.52  tff(c_3509, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3158])).
% 6.85/2.52  tff(c_16, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.85/2.52  tff(c_3515, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_3509, c_16])).
% 6.85/2.52  tff(c_3518, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2600, c_3515])).
% 6.85/2.52  tff(c_3520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_3518])).
% 6.85/2.52  tff(c_3521, plain, (![B_154]: (k3_xboole_0('#skF_2', B_154)='#skF_2')), inference(splitRight, [status(thm)], [c_3158])).
% 6.85/2.52  tff(c_1578, plain, (![B_174]: (k4_xboole_0('#skF_2', B_174)=k3_xboole_0('#skF_2', B_174))), inference(superposition, [status(thm), theory('equality')], [c_1571, c_1146])).
% 6.85/2.52  tff(c_3529, plain, (![B_174]: (k4_xboole_0('#skF_2', B_174)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3521, c_1578])).
% 6.85/2.52  tff(c_2363, plain, (![B_210]: (k4_xboole_0('#skF_2', B_210)=k3_xboole_0(B_210, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2352, c_1146])).
% 6.85/2.52  tff(c_3638, plain, (![B_210]: (k3_xboole_0(B_210, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3529, c_2363])).
% 6.85/2.52  tff(c_2256, plain, (k4_xboole_0(k1_tarski('#skF_1'), k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2217])).
% 6.85/2.52  tff(c_2268, plain, (k4_xboole_0(k1_tarski('#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_4, c_2, c_2256])).
% 6.85/2.52  tff(c_3676, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_2268])).
% 6.85/2.52  tff(c_1294, plain, (![B_56]: (k3_xboole_0('#skF_2', k1_tarski(B_56))='#skF_2')), inference(resolution, [status(thm)], [c_1056, c_1275])).
% 6.85/2.52  tff(c_2391, plain, (![B_56]: (k5_xboole_0(k1_tarski(B_56), '#skF_2')=k4_xboole_0(k1_tarski(B_56), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_2352])).
% 6.85/2.52  tff(c_2412, plain, (![B_56]: (k4_xboole_0(k1_tarski(B_56), '#skF_2')=k1_tarski(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_2391])).
% 6.85/2.52  tff(c_3759, plain, (k1_tarski('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3676, c_2412])).
% 6.85/2.52  tff(c_3766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1052, c_3759])).
% 6.85/2.52  tff(c_3767, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 6.85/2.52  tff(c_3768, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 6.85/2.52  tff(c_56, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.85/2.52  tff(c_3935, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_3768, c_56])).
% 6.85/2.52  tff(c_3839, plain, (![B_270, A_271]: (k5_xboole_0(B_270, A_271)=k5_xboole_0(A_271, B_270))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.85/2.52  tff(c_3855, plain, (![A_271]: (k5_xboole_0(k1_xboole_0, A_271)=A_271)), inference(superposition, [status(thm), theory('equality')], [c_3839, c_22])).
% 6.85/2.52  tff(c_5452, plain, (![A_350, B_351, C_352]: (k5_xboole_0(k5_xboole_0(A_350, B_351), C_352)=k5_xboole_0(A_350, k5_xboole_0(B_351, C_352)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.85/2.52  tff(c_5516, plain, (![A_26, C_352]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_352))=k5_xboole_0(k1_xboole_0, C_352))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5452])).
% 6.85/2.52  tff(c_5530, plain, (![A_353, C_354]: (k5_xboole_0(A_353, k5_xboole_0(A_353, C_354))=C_354)), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_5516])).
% 6.85/2.52  tff(c_5573, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5530])).
% 6.85/2.52  tff(c_3796, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_58])).
% 6.85/2.52  tff(c_5339, plain, (![A_347, B_348]: (k4_xboole_0(k2_xboole_0(A_347, B_348), k3_xboole_0(A_347, B_348))=k5_xboole_0(A_347, B_348))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.85/2.52  tff(c_5390, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3796, c_5339])).
% 6.85/2.52  tff(c_5404, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_5390])).
% 6.85/2.52  tff(c_4441, plain, (![A_303, B_304]: (k5_xboole_0(A_303, k3_xboole_0(A_303, B_304))=k4_xboole_0(A_303, B_304))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.85/2.52  tff(c_6433, plain, (![A_385, B_386]: (k5_xboole_0(A_385, k3_xboole_0(B_386, A_385))=k4_xboole_0(A_385, B_386))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4441])).
% 6.85/2.52  tff(c_5529, plain, (![A_26, C_352]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_352))=C_352)), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_5516])).
% 6.85/2.52  tff(c_9758, plain, (![A_446, B_447]: (k5_xboole_0(A_446, k4_xboole_0(A_446, B_447))=k3_xboole_0(B_447, A_446))), inference(superposition, [status(thm), theory('equality')], [c_6433, c_5529])).
% 6.85/2.52  tff(c_9841, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5404, c_9758])).
% 6.85/2.52  tff(c_9893, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5573, c_2, c_9841])).
% 6.85/2.52  tff(c_4012, plain, (![A_281, B_282, C_283]: (r1_tarski(k3_xboole_0(A_281, B_282), k2_xboole_0(A_281, C_283)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.85/2.52  tff(c_4024, plain, (![B_282]: (r1_tarski(k3_xboole_0('#skF_2', B_282), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3796, c_4012])).
% 6.85/2.52  tff(c_4869, plain, (![B_322, A_323]: (k1_tarski(B_322)=A_323 | k1_xboole_0=A_323 | ~r1_tarski(A_323, k1_tarski(B_322)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.85/2.52  tff(c_4879, plain, (![A_323]: (k1_tarski('#skF_1')=A_323 | k1_xboole_0=A_323 | ~r1_tarski(A_323, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3768, c_4869])).
% 6.85/2.52  tff(c_4911, plain, (![A_325]: (A_325='#skF_2' | k1_xboole_0=A_325 | ~r1_tarski(A_325, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_4879])).
% 6.85/2.52  tff(c_4930, plain, (![B_282]: (k3_xboole_0('#skF_2', B_282)='#skF_2' | k3_xboole_0('#skF_2', B_282)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4024, c_4911])).
% 6.85/2.52  tff(c_9941, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9893, c_4930])).
% 6.85/2.52  tff(c_9966, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9893, c_9941])).
% 6.85/2.52  tff(c_9968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3767, c_3935, c_9966])).
% 6.85/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.52  
% 6.85/2.52  Inference rules
% 6.85/2.52  ----------------------
% 6.85/2.52  #Ref     : 0
% 6.85/2.52  #Sup     : 2416
% 6.85/2.52  #Fact    : 3
% 6.85/2.52  #Define  : 0
% 6.85/2.52  #Split   : 5
% 6.85/2.52  #Chain   : 0
% 6.85/2.52  #Close   : 0
% 6.85/2.52  
% 6.85/2.52  Ordering : KBO
% 6.85/2.52  
% 6.85/2.52  Simplification rules
% 6.85/2.52  ----------------------
% 6.85/2.52  #Subsume      : 68
% 6.85/2.52  #Demod        : 1775
% 6.85/2.52  #Tautology    : 1681
% 6.85/2.52  #SimpNegUnit  : 55
% 6.85/2.52  #BackRed      : 62
% 6.85/2.52  
% 6.85/2.52  #Partial instantiations: 0
% 6.85/2.52  #Strategies tried      : 1
% 6.85/2.52  
% 6.85/2.52  Timing (in seconds)
% 6.85/2.52  ----------------------
% 6.85/2.53  Preprocessing        : 0.32
% 6.85/2.53  Parsing              : 0.17
% 6.85/2.53  CNF conversion       : 0.02
% 6.85/2.53  Main loop            : 1.43
% 6.85/2.53  Inferencing          : 0.43
% 6.85/2.53  Reduction            : 0.65
% 6.85/2.53  Demodulation         : 0.53
% 6.85/2.53  BG Simplification    : 0.05
% 6.85/2.53  Subsumption          : 0.21
% 6.85/2.53  Abstraction          : 0.06
% 6.85/2.53  MUC search           : 0.00
% 6.85/2.53  Cooper               : 0.00
% 6.85/2.53  Total                : 1.79
% 6.85/2.53  Index Insertion      : 0.00
% 6.85/2.53  Index Deletion       : 0.00
% 6.85/2.53  Index Matching       : 0.00
% 6.85/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
