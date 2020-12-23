%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 166 expanded)
%              Number of leaves         :   48 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  160 ( 284 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_72,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_84,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_66,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( r1_tarski(C_15,'#skF_3'(A_13,B_14,C_15))
      | k2_xboole_0(A_13,C_15) = B_14
      | ~ r1_tarski(C_15,B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2546,plain,(
    ! [B_206,A_207,C_208] :
      ( ~ r1_tarski(B_206,'#skF_3'(A_207,B_206,C_208))
      | k2_xboole_0(A_207,C_208) = B_206
      | ~ r1_tarski(C_208,B_206)
      | ~ r1_tarski(A_207,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2554,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(B_14,B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_2546])).

tff(c_2581,plain,(
    ! [A_209,B_210] :
      ( k2_xboole_0(A_209,B_210) = B_210
      | ~ r1_tarski(A_209,B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2554])).

tff(c_2679,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_66,c_2581])).

tff(c_793,plain,(
    ! [A_143,B_144] :
      ( k2_xboole_0(k2_relat_1(A_143),k2_relat_1(B_144)) = k2_relat_1(k2_xboole_0(A_143,B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7536,plain,(
    ! [A_314,B_315] :
      ( r1_tarski(k2_relat_1(A_314),k2_relat_1(k2_xboole_0(A_314,B_315)))
      | ~ v1_relat_1(B_315)
      | ~ v1_relat_1(A_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_34])).

tff(c_7589,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2679,c_7536])).

tff(c_7635,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7589])).

tff(c_280,plain,(
    ! [A_101] :
      ( k2_xboole_0(k1_relat_1(A_101),k2_relat_1(A_101)) = k3_relat_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,k2_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_286,plain,(
    ! [A_10,A_101] :
      ( r1_tarski(A_10,k3_relat_1(A_101))
      | ~ r1_tarski(A_10,k2_relat_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_14])).

tff(c_58,plain,(
    ! [A_60] :
      ( k2_xboole_0(k1_relat_1(A_60),k2_relat_1(A_60)) = k3_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1326,plain,(
    ! [C_165,A_166] :
      ( r2_hidden(k4_tarski(C_165,'#skF_7'(A_166,k1_relat_1(A_166),C_165)),A_166)
      | ~ r2_hidden(C_165,k1_relat_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_147,plain,(
    ! [A_88] : k4_xboole_0(A_88,A_88) = k3_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_157,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_24])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_174,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_170])).

tff(c_1341,plain,(
    ! [C_167] : ~ r2_hidden(C_167,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1326,c_174])).

tff(c_1361,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1341])).

tff(c_596,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(k2_xboole_0(A_136,C_137),B_138)
      | ~ r1_tarski(C_137,B_138)
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_247,plain,(
    ! [B_98,A_99] :
      ( B_98 = A_99
      | ~ r1_tarski(B_98,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_259,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(k2_xboole_0(A_28,B_29),A_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_604,plain,(
    ! [B_138,C_137] :
      ( k2_xboole_0(B_138,C_137) = B_138
      | ~ r1_tarski(C_137,B_138)
      | ~ r1_tarski(B_138,B_138) ) ),
    inference(resolution,[status(thm)],[c_596,c_259])).

tff(c_709,plain,(
    ! [B_140,C_141] :
      ( k2_xboole_0(B_140,C_141) = B_140
      | ~ r1_tarski(C_141,B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_604])).

tff(c_752,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(resolution,[status(thm)],[c_22,c_709])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(k4_xboole_0(A_19,B_20),C_21)
      | ~ r1_tarski(A_19,k2_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_824,plain,(
    ! [A_145] : k2_xboole_0(A_145,k1_xboole_0) = A_145 ),
    inference(resolution,[status(thm)],[c_22,c_709])).

tff(c_894,plain,(
    ! [A_146,A_147] :
      ( r1_tarski(A_146,A_147)
      | ~ r1_tarski(A_146,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_14])).

tff(c_900,plain,(
    ! [A_19,B_20,A_147] :
      ( r1_tarski(k4_xboole_0(A_19,B_20),A_147)
      | ~ r1_tarski(A_19,k2_xboole_0(B_20,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_26,c_894])).

tff(c_1059,plain,(
    ! [A_155,B_156,A_157] :
      ( r1_tarski(k4_xboole_0(A_155,B_156),A_157)
      | ~ r1_tarski(A_155,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_900])).

tff(c_264,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_247])).

tff(c_1107,plain,(
    ! [A_160,B_161] :
      ( k4_xboole_0(A_160,B_161) = k1_xboole_0
      | ~ r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_1059,c_264])).

tff(c_1164,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_1107])).

tff(c_42,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    ! [A_61,B_63] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_61),k1_relat_1(B_63)),k1_relat_1(k6_subset_1(A_61,B_63)))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1480,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_171),k1_relat_1(B_172)),k1_relat_1(k4_xboole_0(A_171,B_172)))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_60])).

tff(c_1503,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_1480])).

tff(c_1528,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1361,c_1503])).

tff(c_1723,plain,(
    k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1528,c_264])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,k2_xboole_0(B_23,C_24))
      | ~ r1_tarski(k4_xboole_0(A_22,B_23),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1764,plain,(
    ! [C_24] :
      ( r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),C_24))
      | ~ r1_tarski(k1_xboole_0,C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_28])).

tff(c_1946,plain,(
    ! [C_190] : r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),C_190)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1764])).

tff(c_1966,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1946])).

tff(c_1973,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1966])).

tff(c_10178,plain,(
    ! [A_363,B_364] :
      ( r1_tarski(k3_relat_1(A_363),B_364)
      | ~ r1_tarski(k2_relat_1(A_363),B_364)
      | ~ r1_tarski(k1_relat_1(A_363),B_364)
      | ~ v1_relat_1(A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_596])).

tff(c_64,plain,(
    ~ r1_tarski(k3_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10264,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10178,c_64])).

tff(c_10298,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1973,c_10264])).

tff(c_10306,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_286,c_10298])).

tff(c_10313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7635,c_10306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:22:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.20/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.57  
% 7.20/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 7.20/2.58  
% 7.20/2.58  %Foreground sorts:
% 7.20/2.58  
% 7.20/2.58  
% 7.20/2.58  %Background operators:
% 7.20/2.58  
% 7.20/2.58  
% 7.20/2.58  %Foreground operators:
% 7.20/2.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.20/2.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.20/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.20/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.20/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.20/2.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.20/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.20/2.58  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.20/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.20/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.20/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.20/2.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.20/2.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.20/2.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.20/2.58  tff('#skF_9', type, '#skF_9': $i).
% 7.20/2.58  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.20/2.58  tff('#skF_8', type, '#skF_8': $i).
% 7.20/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.20/2.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.20/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.20/2.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.20/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.20/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.20/2.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.20/2.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.20/2.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.20/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.20/2.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.20/2.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.20/2.58  
% 7.20/2.60  tff(f_138, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.20/2.60  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.20/2.60  tff(f_70, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 7.20/2.60  tff(f_128, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 7.20/2.60  tff(f_88, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.20/2.60  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.20/2.60  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.20/2.60  tff(f_72, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.20/2.60  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.20/2.60  tff(f_110, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.20/2.60  tff(f_86, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.20/2.60  tff(f_74, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.20/2.60  tff(f_84, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.20/2.60  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.20/2.60  tff(f_94, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.20/2.60  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.20/2.60  tff(f_100, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.20/2.60  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 7.20/2.60  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.20/2.60  tff(c_68, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.20/2.60  tff(c_70, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.20/2.60  tff(c_66, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.20/2.60  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.20/2.60  tff(c_18, plain, (![C_15, A_13, B_14]: (r1_tarski(C_15, '#skF_3'(A_13, B_14, C_15)) | k2_xboole_0(A_13, C_15)=B_14 | ~r1_tarski(C_15, B_14) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.20/2.60  tff(c_2546, plain, (![B_206, A_207, C_208]: (~r1_tarski(B_206, '#skF_3'(A_207, B_206, C_208)) | k2_xboole_0(A_207, C_208)=B_206 | ~r1_tarski(C_208, B_206) | ~r1_tarski(A_207, B_206))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.20/2.60  tff(c_2554, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(B_14, B_14) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_2546])).
% 7.20/2.60  tff(c_2581, plain, (![A_209, B_210]: (k2_xboole_0(A_209, B_210)=B_210 | ~r1_tarski(A_209, B_210))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2554])).
% 7.20/2.60  tff(c_2679, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_66, c_2581])).
% 7.20/2.60  tff(c_793, plain, (![A_143, B_144]: (k2_xboole_0(k2_relat_1(A_143), k2_relat_1(B_144))=k2_relat_1(k2_xboole_0(A_143, B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.20/2.60  tff(c_34, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.20/2.60  tff(c_7536, plain, (![A_314, B_315]: (r1_tarski(k2_relat_1(A_314), k2_relat_1(k2_xboole_0(A_314, B_315))) | ~v1_relat_1(B_315) | ~v1_relat_1(A_314))), inference(superposition, [status(thm), theory('equality')], [c_793, c_34])).
% 7.20/2.60  tff(c_7589, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2679, c_7536])).
% 7.20/2.60  tff(c_7635, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7589])).
% 7.20/2.60  tff(c_280, plain, (![A_101]: (k2_xboole_0(k1_relat_1(A_101), k2_relat_1(A_101))=k3_relat_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.20/2.60  tff(c_14, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, k2_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.20/2.60  tff(c_286, plain, (![A_10, A_101]: (r1_tarski(A_10, k3_relat_1(A_101)) | ~r1_tarski(A_10, k2_relat_1(A_101)) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_280, c_14])).
% 7.20/2.60  tff(c_58, plain, (![A_60]: (k2_xboole_0(k1_relat_1(A_60), k2_relat_1(A_60))=k3_relat_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.20/2.60  tff(c_22, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.20/2.60  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.20/2.60  tff(c_1326, plain, (![C_165, A_166]: (r2_hidden(k4_tarski(C_165, '#skF_7'(A_166, k1_relat_1(A_166), C_165)), A_166) | ~r2_hidden(C_165, k1_relat_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.20/2.60  tff(c_32, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.20/2.60  tff(c_24, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.20/2.60  tff(c_129, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_147, plain, (![A_88]: (k4_xboole_0(A_88, A_88)=k3_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_129])).
% 7.20/2.60  tff(c_157, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_147, c_24])).
% 7.20/2.60  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.20/2.60  tff(c_170, plain, (![C_5]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 7.20/2.60  tff(c_174, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_170])).
% 7.20/2.60  tff(c_1341, plain, (![C_167]: (~r2_hidden(C_167, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1326, c_174])).
% 7.20/2.60  tff(c_1361, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1341])).
% 7.20/2.60  tff(c_596, plain, (![A_136, C_137, B_138]: (r1_tarski(k2_xboole_0(A_136, C_137), B_138) | ~r1_tarski(C_137, B_138) | ~r1_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.20/2.60  tff(c_247, plain, (![B_98, A_99]: (B_98=A_99 | ~r1_tarski(B_98, A_99) | ~r1_tarski(A_99, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.20/2.60  tff(c_259, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(k2_xboole_0(A_28, B_29), A_28))), inference(resolution, [status(thm)], [c_34, c_247])).
% 7.20/2.60  tff(c_604, plain, (![B_138, C_137]: (k2_xboole_0(B_138, C_137)=B_138 | ~r1_tarski(C_137, B_138) | ~r1_tarski(B_138, B_138))), inference(resolution, [status(thm)], [c_596, c_259])).
% 7.20/2.60  tff(c_709, plain, (![B_140, C_141]: (k2_xboole_0(B_140, C_141)=B_140 | ~r1_tarski(C_141, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_604])).
% 7.20/2.60  tff(c_752, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(resolution, [status(thm)], [c_22, c_709])).
% 7.20/2.60  tff(c_26, plain, (![A_19, B_20, C_21]: (r1_tarski(k4_xboole_0(A_19, B_20), C_21) | ~r1_tarski(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.20/2.60  tff(c_824, plain, (![A_145]: (k2_xboole_0(A_145, k1_xboole_0)=A_145)), inference(resolution, [status(thm)], [c_22, c_709])).
% 7.20/2.60  tff(c_894, plain, (![A_146, A_147]: (r1_tarski(A_146, A_147) | ~r1_tarski(A_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_824, c_14])).
% 7.20/2.60  tff(c_900, plain, (![A_19, B_20, A_147]: (r1_tarski(k4_xboole_0(A_19, B_20), A_147) | ~r1_tarski(A_19, k2_xboole_0(B_20, k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_894])).
% 7.20/2.60  tff(c_1059, plain, (![A_155, B_156, A_157]: (r1_tarski(k4_xboole_0(A_155, B_156), A_157) | ~r1_tarski(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_900])).
% 7.20/2.60  tff(c_264, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_247])).
% 7.20/2.60  tff(c_1107, plain, (![A_160, B_161]: (k4_xboole_0(A_160, B_161)=k1_xboole_0 | ~r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_1059, c_264])).
% 7.20/2.60  tff(c_1164, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_1107])).
% 7.20/2.60  tff(c_42, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.20/2.60  tff(c_60, plain, (![A_61, B_63]: (r1_tarski(k6_subset_1(k1_relat_1(A_61), k1_relat_1(B_63)), k1_relat_1(k6_subset_1(A_61, B_63))) | ~v1_relat_1(B_63) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.20/2.60  tff(c_1480, plain, (![A_171, B_172]: (r1_tarski(k4_xboole_0(k1_relat_1(A_171), k1_relat_1(B_172)), k1_relat_1(k4_xboole_0(A_171, B_172))) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_60])).
% 7.20/2.60  tff(c_1503, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1164, c_1480])).
% 7.20/2.60  tff(c_1528, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1361, c_1503])).
% 7.20/2.60  tff(c_1723, plain, (k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1528, c_264])).
% 7.20/2.60  tff(c_28, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, k2_xboole_0(B_23, C_24)) | ~r1_tarski(k4_xboole_0(A_22, B_23), C_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.20/2.60  tff(c_1764, plain, (![C_24]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), C_24)) | ~r1_tarski(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_1723, c_28])).
% 7.20/2.60  tff(c_1946, plain, (![C_190]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), C_190)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1764])).
% 7.20/2.60  tff(c_1966, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1946])).
% 7.20/2.60  tff(c_1973, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1966])).
% 7.20/2.60  tff(c_10178, plain, (![A_363, B_364]: (r1_tarski(k3_relat_1(A_363), B_364) | ~r1_tarski(k2_relat_1(A_363), B_364) | ~r1_tarski(k1_relat_1(A_363), B_364) | ~v1_relat_1(A_363))), inference(superposition, [status(thm), theory('equality')], [c_58, c_596])).
% 7.20/2.60  tff(c_64, plain, (~r1_tarski(k3_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.20/2.60  tff(c_10264, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10178, c_64])).
% 7.20/2.60  tff(c_10298, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1973, c_10264])).
% 7.20/2.60  tff(c_10306, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_286, c_10298])).
% 7.20/2.60  tff(c_10313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_7635, c_10306])).
% 7.20/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.60  
% 7.20/2.60  Inference rules
% 7.20/2.60  ----------------------
% 7.20/2.60  #Ref     : 0
% 7.20/2.60  #Sup     : 2483
% 7.20/2.60  #Fact    : 0
% 7.20/2.60  #Define  : 0
% 7.20/2.60  #Split   : 6
% 7.20/2.60  #Chain   : 0
% 7.20/2.60  #Close   : 0
% 7.20/2.60  
% 7.20/2.60  Ordering : KBO
% 7.20/2.60  
% 7.20/2.60  Simplification rules
% 7.20/2.60  ----------------------
% 7.20/2.60  #Subsume      : 384
% 7.20/2.60  #Demod        : 1603
% 7.20/2.60  #Tautology    : 1194
% 7.20/2.60  #SimpNegUnit  : 6
% 7.20/2.60  #BackRed      : 10
% 7.20/2.60  
% 7.20/2.60  #Partial instantiations: 0
% 7.20/2.60  #Strategies tried      : 1
% 7.20/2.60  
% 7.20/2.60  Timing (in seconds)
% 7.20/2.60  ----------------------
% 7.20/2.60  Preprocessing        : 0.36
% 7.20/2.60  Parsing              : 0.19
% 7.20/2.60  CNF conversion       : 0.03
% 7.20/2.60  Main loop            : 1.48
% 7.20/2.60  Inferencing          : 0.43
% 7.20/2.60  Reduction            : 0.58
% 7.20/2.60  Demodulation         : 0.46
% 7.20/2.60  BG Simplification    : 0.05
% 7.20/2.60  Subsumption          : 0.32
% 7.20/2.60  Abstraction          : 0.06
% 7.20/2.60  MUC search           : 0.00
% 7.20/2.60  Cooper               : 0.00
% 7.20/2.60  Total                : 1.88
% 7.20/2.60  Index Insertion      : 0.00
% 7.20/2.60  Index Deletion       : 0.00
% 7.20/2.60  Index Matching       : 0.00
% 7.20/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
