%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 9.98s
% Output     : CNFRefutation 9.98s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 265 expanded)
%              Number of leaves         :   50 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 ( 449 expanded)
%              Number of equality atoms :   44 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_89,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_119,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_137,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_84,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_82,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,(
    ! [A_81] :
      ( k2_xboole_0(k1_relat_1(A_81),k2_relat_1(A_81)) = k3_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_580,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(A_142,C_143)
      | ~ r1_tarski(B_144,C_143)
      | ~ r1_tarski(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_602,plain,(
    ! [A_145,A_146] :
      ( r1_tarski(A_145,A_146)
      | ~ r1_tarski(A_145,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_580])).

tff(c_605,plain,(
    ! [A_12,A_146] :
      ( r1_tarski(A_12,A_146)
      | k4_xboole_0(A_12,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_602])).

tff(c_618,plain,(
    ! [A_146] : r1_tarski(k1_xboole_0,A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_605])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2538,plain,(
    ! [C_237,A_238] :
      ( r2_hidden(k4_tarski(C_237,'#skF_6'(A_238,k1_relat_1(A_238),C_237)),A_238)
      | ~ r2_hidden(C_237,k1_relat_1(A_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_327,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,k3_xboole_0(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_333,plain,(
    ! [A_120,B_121] :
      ( ~ r1_xboole_0(A_120,B_121)
      | k3_xboole_0(A_120,B_121) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_327])).

tff(c_360,plain,(
    ! [A_124] : k3_xboole_0(A_124,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_333])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_365,plain,(
    ! [A_124,C_7] :
      ( ~ r1_xboole_0(A_124,k1_xboole_0)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_6])).

tff(c_370,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_365])).

tff(c_620,plain,(
    ! [A_147,A_148] :
      ( r1_tarski(A_147,A_148)
      | k1_xboole_0 != A_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_605])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_669,plain,(
    ! [A_153,A_154] :
      ( k4_xboole_0(A_153,A_154) = k1_xboole_0
      | k1_xboole_0 != A_153 ) ),
    inference(resolution,[status(thm)],[c_620,c_18])).

tff(c_34,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_679,plain,(
    ! [A_153,B_30] :
      ( k3_xboole_0(A_153,B_30) = k1_xboole_0
      | k1_xboole_0 != A_153 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_34])).

tff(c_1411,plain,(
    ! [A_191,B_192] :
      ( r2_hidden('#skF_1'(A_191,B_192),k3_xboole_0(A_191,B_192))
      | r1_xboole_0(A_191,B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1417,plain,(
    ! [A_153,B_30] :
      ( r2_hidden('#skF_1'(A_153,B_30),k1_xboole_0)
      | r1_xboole_0(A_153,B_30)
      | k1_xboole_0 != A_153 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_1411])).

tff(c_1449,plain,(
    ! [A_193,B_194] :
      ( r1_xboole_0(A_193,B_194)
      | k1_xboole_0 != A_193 ) ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_1417])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k1_xboole_0
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_182])).

tff(c_398,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k4_xboole_0(A_129,B_130)) = k3_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_423,plain,(
    ! [B_11] : k4_xboole_0(B_11,k1_xboole_0) = k3_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_398])).

tff(c_463,plain,(
    ! [B_132] : k3_xboole_0(B_132,B_132) = B_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_423])).

tff(c_477,plain,(
    ! [B_132,C_7] :
      ( ~ r1_xboole_0(B_132,B_132)
      | ~ r2_hidden(C_7,B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_6])).

tff(c_1459,plain,(
    ! [C_7,B_194] :
      ( ~ r2_hidden(C_7,B_194)
      | k1_xboole_0 != B_194 ) ),
    inference(resolution,[status(thm)],[c_1449,c_477])).

tff(c_2677,plain,(
    ! [A_244,C_245] :
      ( k1_xboole_0 != A_244
      | ~ r2_hidden(C_245,k1_relat_1(A_244)) ) ),
    inference(resolution,[status(thm)],[c_2538,c_1459])).

tff(c_2698,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_2677])).

tff(c_80,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_201,plain,(
    k4_xboole_0('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_182])).

tff(c_44,plain,(
    ! [A_39,B_40] : k6_subset_1(A_39,B_40) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    ! [A_82,B_84] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_82),k1_relat_1(B_84)),k1_relat_1(k6_subset_1(A_82,B_84)))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3128,plain,(
    ! [A_256,B_257] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_256),k1_relat_1(B_257)),k1_relat_1(k4_xboole_0(A_256,B_257)))
      | ~ v1_relat_1(B_257)
      | ~ v1_relat_1(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_74])).

tff(c_3194,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_3128])).

tff(c_3223,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2698,c_3194])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_644,plain,(
    ! [A_148,A_147] :
      ( A_148 = A_147
      | ~ r1_tarski(A_148,A_147)
      | k1_xboole_0 != A_147 ) ),
    inference(resolution,[status(thm)],[c_620,c_10])).

tff(c_3328,plain,(
    k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3223,c_644])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,k2_xboole_0(B_27,C_28))
      | ~ r1_tarski(k4_xboole_0(A_26,B_27),C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3380,plain,(
    ! [C_28] :
      ( r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_28))
      | ~ r1_tarski(k1_xboole_0,C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3328,c_32])).

tff(c_6172,plain,(
    ! [C_342] : r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_342)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_3380])).

tff(c_6218,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6172])).

tff(c_6246,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6218])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2371,plain,(
    ! [A_229,C_230] :
      ( r2_hidden(k4_tarski('#skF_10'(A_229,k2_relat_1(A_229),C_230),C_230),A_229)
      | ~ r2_hidden(C_230,k2_relat_1(A_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2497,plain,(
    ! [A_234,C_235] :
      ( k1_xboole_0 != A_234
      | ~ r2_hidden(C_235,k2_relat_1(A_234)) ) ),
    inference(resolution,[status(thm)],[c_2371,c_1459])).

tff(c_2512,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_2497])).

tff(c_76,plain,(
    ! [A_85,B_87] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_85),k2_relat_1(B_87)),k2_relat_1(k6_subset_1(A_85,B_87)))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3421,plain,(
    ! [A_261,B_262] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_261),k2_relat_1(B_262)),k2_relat_1(k4_xboole_0(A_261,B_262)))
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_76])).

tff(c_3490,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_3421])).

tff(c_3520,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2512,c_3490])).

tff(c_3588,plain,(
    k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3520,c_644])).

tff(c_3643,plain,(
    ! [C_28] :
      ( r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),C_28))
      | ~ r1_tarski(k1_xboole_0,C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3588,c_32])).

tff(c_5733,plain,(
    ! [C_334] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),C_334)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_3643])).

tff(c_9394,plain,(
    ! [B_383] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(B_383,k2_relat_1('#skF_12'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5733])).

tff(c_9439,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_9394])).

tff(c_9462,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9439])).

tff(c_1783,plain,(
    ! [A_205,C_206,B_207] :
      ( r1_tarski(k2_xboole_0(A_205,C_206),B_207)
      | ~ r1_tarski(C_206,B_207)
      | ~ r1_tarski(A_205,B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_21653,plain,(
    ! [A_556,B_557] :
      ( r1_tarski(k3_relat_1(A_556),B_557)
      | ~ r1_tarski(k2_relat_1(A_556),B_557)
      | ~ r1_tarski(k1_relat_1(A_556),B_557)
      | ~ v1_relat_1(A_556) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1783])).

tff(c_78,plain,(
    ~ r1_tarski(k3_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_21737,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_21653,c_78])).

tff(c_21773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6246,c_9462,c_21737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.98/4.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/4.02  
% 9.98/4.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/4.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 9.98/4.02  
% 9.98/4.02  %Foreground sorts:
% 9.98/4.02  
% 9.98/4.02  
% 9.98/4.02  %Background operators:
% 9.98/4.02  
% 9.98/4.02  
% 9.98/4.02  %Foreground operators:
% 9.98/4.02  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.98/4.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.98/4.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.98/4.02  tff('#skF_11', type, '#skF_11': $i).
% 9.98/4.02  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.98/4.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.98/4.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.98/4.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.98/4.02  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.98/4.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.98/4.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.98/4.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.98/4.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.98/4.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.98/4.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.98/4.02  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.98/4.02  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.98/4.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.98/4.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.98/4.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.98/4.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.98/4.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.98/4.02  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.98/4.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.98/4.02  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.98/4.02  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.98/4.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.98/4.02  tff('#skF_12', type, '#skF_12': $i).
% 9.98/4.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.98/4.02  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.98/4.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.98/4.02  
% 9.98/4.04  tff(f_147, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 9.98/4.04  tff(f_123, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 9.98/4.04  tff(f_73, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.98/4.04  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.98/4.04  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.98/4.04  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.98/4.04  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.98/4.04  tff(f_111, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 9.98/4.04  tff(f_89, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.98/4.04  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.98/4.04  tff(f_87, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.98/4.04  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.98/4.04  tff(f_101, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.98/4.04  tff(f_130, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 9.98/4.04  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.98/4.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.98/4.04  tff(f_119, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 9.98/4.04  tff(f_137, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 9.98/4.04  tff(f_97, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 9.98/4.04  tff(c_84, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.98/4.04  tff(c_82, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.98/4.04  tff(c_72, plain, (![A_81]: (k2_xboole_0(k1_relat_1(A_81), k2_relat_1(A_81))=k3_relat_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.98/4.04  tff(c_26, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.98/4.04  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.98/4.04  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.98/4.04  tff(c_580, plain, (![A_142, C_143, B_144]: (r1_tarski(A_142, C_143) | ~r1_tarski(B_144, C_143) | ~r1_tarski(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.98/4.04  tff(c_602, plain, (![A_145, A_146]: (r1_tarski(A_145, A_146) | ~r1_tarski(A_145, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_580])).
% 9.98/4.04  tff(c_605, plain, (![A_12, A_146]: (r1_tarski(A_12, A_146) | k4_xboole_0(A_12, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_602])).
% 9.98/4.04  tff(c_618, plain, (![A_146]: (r1_tarski(k1_xboole_0, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_605])).
% 9.98/4.04  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.98/4.04  tff(c_2538, plain, (![C_237, A_238]: (r2_hidden(k4_tarski(C_237, '#skF_6'(A_238, k1_relat_1(A_238), C_237)), A_238) | ~r2_hidden(C_237, k1_relat_1(A_238)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.98/4.04  tff(c_36, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.98/4.04  tff(c_327, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, k3_xboole_0(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.98/4.04  tff(c_333, plain, (![A_120, B_121]: (~r1_xboole_0(A_120, B_121) | k3_xboole_0(A_120, B_121)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_327])).
% 9.98/4.04  tff(c_360, plain, (![A_124]: (k3_xboole_0(A_124, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_333])).
% 9.98/4.04  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.98/4.04  tff(c_365, plain, (![A_124, C_7]: (~r1_xboole_0(A_124, k1_xboole_0) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_360, c_6])).
% 9.98/4.04  tff(c_370, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_365])).
% 9.98/4.04  tff(c_620, plain, (![A_147, A_148]: (r1_tarski(A_147, A_148) | k1_xboole_0!=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_605])).
% 9.98/4.04  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.98/4.04  tff(c_669, plain, (![A_153, A_154]: (k4_xboole_0(A_153, A_154)=k1_xboole_0 | k1_xboole_0!=A_153)), inference(resolution, [status(thm)], [c_620, c_18])).
% 9.98/4.04  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.98/4.04  tff(c_679, plain, (![A_153, B_30]: (k3_xboole_0(A_153, B_30)=k1_xboole_0 | k1_xboole_0!=A_153)), inference(superposition, [status(thm), theory('equality')], [c_669, c_34])).
% 9.98/4.04  tff(c_1411, plain, (![A_191, B_192]: (r2_hidden('#skF_1'(A_191, B_192), k3_xboole_0(A_191, B_192)) | r1_xboole_0(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.98/4.04  tff(c_1417, plain, (![A_153, B_30]: (r2_hidden('#skF_1'(A_153, B_30), k1_xboole_0) | r1_xboole_0(A_153, B_30) | k1_xboole_0!=A_153)), inference(superposition, [status(thm), theory('equality')], [c_679, c_1411])).
% 9.98/4.04  tff(c_1449, plain, (![A_193, B_194]: (r1_xboole_0(A_193, B_194) | k1_xboole_0!=A_193)), inference(negUnitSimplification, [status(thm)], [c_370, c_1417])).
% 9.98/4.04  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.98/4.04  tff(c_182, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k1_xboole_0 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.98/4.04  tff(c_202, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_182])).
% 9.98/4.04  tff(c_398, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k4_xboole_0(A_129, B_130))=k3_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.98/4.04  tff(c_423, plain, (![B_11]: (k4_xboole_0(B_11, k1_xboole_0)=k3_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_202, c_398])).
% 9.98/4.04  tff(c_463, plain, (![B_132]: (k3_xboole_0(B_132, B_132)=B_132)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_423])).
% 9.98/4.04  tff(c_477, plain, (![B_132, C_7]: (~r1_xboole_0(B_132, B_132) | ~r2_hidden(C_7, B_132))), inference(superposition, [status(thm), theory('equality')], [c_463, c_6])).
% 9.98/4.04  tff(c_1459, plain, (![C_7, B_194]: (~r2_hidden(C_7, B_194) | k1_xboole_0!=B_194)), inference(resolution, [status(thm)], [c_1449, c_477])).
% 9.98/4.04  tff(c_2677, plain, (![A_244, C_245]: (k1_xboole_0!=A_244 | ~r2_hidden(C_245, k1_relat_1(A_244)))), inference(resolution, [status(thm)], [c_2538, c_1459])).
% 9.98/4.04  tff(c_2698, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_2677])).
% 9.98/4.04  tff(c_80, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.98/4.04  tff(c_201, plain, (k4_xboole_0('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_182])).
% 9.98/4.04  tff(c_44, plain, (![A_39, B_40]: (k6_subset_1(A_39, B_40)=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.98/4.04  tff(c_74, plain, (![A_82, B_84]: (r1_tarski(k6_subset_1(k1_relat_1(A_82), k1_relat_1(B_84)), k1_relat_1(k6_subset_1(A_82, B_84))) | ~v1_relat_1(B_84) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.98/4.04  tff(c_3128, plain, (![A_256, B_257]: (r1_tarski(k4_xboole_0(k1_relat_1(A_256), k1_relat_1(B_257)), k1_relat_1(k4_xboole_0(A_256, B_257))) | ~v1_relat_1(B_257) | ~v1_relat_1(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_74])).
% 9.98/4.04  tff(c_3194, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_201, c_3128])).
% 9.98/4.04  tff(c_3223, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2698, c_3194])).
% 9.98/4.04  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.98/4.04  tff(c_644, plain, (![A_148, A_147]: (A_148=A_147 | ~r1_tarski(A_148, A_147) | k1_xboole_0!=A_147)), inference(resolution, [status(thm)], [c_620, c_10])).
% 9.98/4.04  tff(c_3328, plain, (k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3223, c_644])).
% 9.98/4.04  tff(c_32, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, k2_xboole_0(B_27, C_28)) | ~r1_tarski(k4_xboole_0(A_26, B_27), C_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.98/4.04  tff(c_3380, plain, (![C_28]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_28)) | ~r1_tarski(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_3328, c_32])).
% 9.98/4.04  tff(c_6172, plain, (![C_342]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_342)))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_3380])).
% 9.98/4.04  tff(c_6218, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_72, c_6172])).
% 9.98/4.04  tff(c_6246, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6218])).
% 9.98/4.04  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.98/4.04  tff(c_2371, plain, (![A_229, C_230]: (r2_hidden(k4_tarski('#skF_10'(A_229, k2_relat_1(A_229), C_230), C_230), A_229) | ~r2_hidden(C_230, k2_relat_1(A_229)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.98/4.04  tff(c_2497, plain, (![A_234, C_235]: (k1_xboole_0!=A_234 | ~r2_hidden(C_235, k2_relat_1(A_234)))), inference(resolution, [status(thm)], [c_2371, c_1459])).
% 9.98/4.04  tff(c_2512, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_2497])).
% 9.98/4.04  tff(c_76, plain, (![A_85, B_87]: (r1_tarski(k6_subset_1(k2_relat_1(A_85), k2_relat_1(B_87)), k2_relat_1(k6_subset_1(A_85, B_87))) | ~v1_relat_1(B_87) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.98/4.04  tff(c_3421, plain, (![A_261, B_262]: (r1_tarski(k4_xboole_0(k2_relat_1(A_261), k2_relat_1(B_262)), k2_relat_1(k4_xboole_0(A_261, B_262))) | ~v1_relat_1(B_262) | ~v1_relat_1(A_261))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_76])).
% 9.98/4.04  tff(c_3490, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_201, c_3421])).
% 9.98/4.04  tff(c_3520, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2512, c_3490])).
% 9.98/4.04  tff(c_3588, plain, (k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3520, c_644])).
% 9.98/4.04  tff(c_3643, plain, (![C_28]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), C_28)) | ~r1_tarski(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_3588, c_32])).
% 9.98/4.04  tff(c_5733, plain, (![C_334]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), C_334)))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_3643])).
% 9.98/4.04  tff(c_9394, plain, (![B_383]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(B_383, k2_relat_1('#skF_12'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5733])).
% 9.98/4.04  tff(c_9439, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_72, c_9394])).
% 9.98/4.04  tff(c_9462, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9439])).
% 9.98/4.04  tff(c_1783, plain, (![A_205, C_206, B_207]: (r1_tarski(k2_xboole_0(A_205, C_206), B_207) | ~r1_tarski(C_206, B_207) | ~r1_tarski(A_205, B_207))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.98/4.04  tff(c_21653, plain, (![A_556, B_557]: (r1_tarski(k3_relat_1(A_556), B_557) | ~r1_tarski(k2_relat_1(A_556), B_557) | ~r1_tarski(k1_relat_1(A_556), B_557) | ~v1_relat_1(A_556))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1783])).
% 9.98/4.04  tff(c_78, plain, (~r1_tarski(k3_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.98/4.04  tff(c_21737, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_21653, c_78])).
% 9.98/4.04  tff(c_21773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_6246, c_9462, c_21737])).
% 9.98/4.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/4.04  
% 9.98/4.04  Inference rules
% 9.98/4.04  ----------------------
% 9.98/4.04  #Ref     : 1
% 9.98/4.04  #Sup     : 5354
% 9.98/4.04  #Fact    : 0
% 9.98/4.04  #Define  : 0
% 9.98/4.04  #Split   : 10
% 9.98/4.04  #Chain   : 0
% 9.98/4.04  #Close   : 0
% 9.98/4.04  
% 9.98/4.04  Ordering : KBO
% 9.98/4.04  
% 9.98/4.04  Simplification rules
% 9.98/4.04  ----------------------
% 9.98/4.04  #Subsume      : 1334
% 9.98/4.04  #Demod        : 2681
% 9.98/4.04  #Tautology    : 2008
% 9.98/4.04  #SimpNegUnit  : 106
% 9.98/4.04  #BackRed      : 8
% 9.98/4.04  
% 9.98/4.04  #Partial instantiations: 0
% 9.98/4.04  #Strategies tried      : 1
% 9.98/4.04  
% 9.98/4.04  Timing (in seconds)
% 9.98/4.04  ----------------------
% 9.98/4.05  Preprocessing        : 0.34
% 9.98/4.05  Parsing              : 0.17
% 9.98/4.05  CNF conversion       : 0.03
% 9.98/4.05  Main loop            : 2.91
% 9.98/4.05  Inferencing          : 0.58
% 9.98/4.05  Reduction            : 1.33
% 9.98/4.05  Demodulation         : 1.06
% 9.98/4.05  BG Simplification    : 0.07
% 9.98/4.05  Subsumption          : 0.75
% 9.98/4.05  Abstraction          : 0.08
% 9.98/4.05  MUC search           : 0.00
% 9.98/4.05  Cooper               : 0.00
% 9.98/4.05  Total                : 3.29
% 9.98/4.05  Index Insertion      : 0.00
% 9.98/4.05  Index Deletion       : 0.00
% 9.98/4.05  Index Matching       : 0.00
% 9.98/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
