%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:29 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 172 expanded)
%              Number of leaves         :   52 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  154 ( 271 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_85,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_95,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_150,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_32,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1244,plain,(
    ! [A_176,C_177,B_178] :
      ( r1_tarski(k2_xboole_0(A_176,C_177),B_178)
      | ~ r1_tarski(C_177,B_178)
      | ~ r1_tarski(A_176,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_257,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_269,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(k2_xboole_0(A_31,B_32),A_31) ) ),
    inference(resolution,[status(thm)],[c_40,c_257])).

tff(c_1252,plain,(
    ! [B_178,C_177] :
      ( k2_xboole_0(B_178,C_177) = B_178
      | ~ r1_tarski(C_177,B_178)
      | ~ r1_tarski(B_178,B_178) ) ),
    inference(resolution,[status(thm)],[c_1244,c_269])).

tff(c_1280,plain,(
    ! [B_179,C_180] :
      ( k2_xboole_0(B_179,C_180) = B_179
      | ~ r1_tarski(C_180,B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1252])).

tff(c_1330,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(resolution,[status(thm)],[c_32,c_1280])).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    ! [A_78] :
      ( v1_relat_1(A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_70,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_8'(A_68,B_69),k1_relat_1(B_69))
      | ~ r2_hidden(A_68,k2_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2235,plain,(
    ! [C_210,A_211] :
      ( r2_hidden(k4_tarski(C_210,'#skF_7'(A_211,k1_relat_1(A_211),C_210)),A_211)
      | ~ r2_hidden(C_210,k1_relat_1(A_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ! [A_30] : r1_xboole_0(A_30,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_93,plain,(
    ! [B_81,A_82] :
      ( r1_xboole_0(B_81,A_82)
      | ~ r1_xboole_0(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_96,plain,(
    ! [A_30] : r1_xboole_0(k1_xboole_0,A_30) ),
    inference(resolution,[status(thm)],[c_38,c_93])).

tff(c_206,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(A_101,B_102) = A_101
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_224,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_206])).

tff(c_343,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,k3_xboole_0(A_114,B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_355,plain,(
    ! [A_23,C_116] :
      ( ~ r1_xboole_0(k1_xboole_0,A_23)
      | ~ r2_hidden(C_116,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_343])).

tff(c_361,plain,(
    ! [C_116] : ~ r2_hidden(C_116,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_355])).

tff(c_2250,plain,(
    ! [C_212] : ~ r2_hidden(C_212,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2235,c_361])).

tff(c_2262,plain,(
    ! [A_68] :
      ( ~ r2_hidden(A_68,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_70,c_2250])).

tff(c_2314,plain,(
    ! [A_213] : ~ r2_hidden(A_213,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2262])).

tff(c_2334,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2314])).

tff(c_76,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_121,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_136,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_121])).

tff(c_48,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    ! [A_71,B_73] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_71),k2_relat_1(B_73)),k2_relat_1(k6_subset_1(A_71,B_73)))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2439,plain,(
    ! [A_215,B_216] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_215),k2_relat_1(B_216)),k2_relat_1(k4_xboole_0(A_215,B_216)))
      | ~ v1_relat_1(B_216)
      | ~ v1_relat_1(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_72])).

tff(c_2493,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2439])).

tff(c_2519,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2334,c_2493])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,k2_xboole_0(B_28,C_29))
      | ~ r1_tarski(k4_xboole_0(A_27,B_28),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2536,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(k2_relat_1('#skF_10'),k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2519,c_36])).

tff(c_2556,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_2536])).

tff(c_441,plain,(
    ! [A_125] :
      ( k2_xboole_0(k1_relat_1(A_125),k2_relat_1(A_125)) = k3_relat_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,k2_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_447,plain,(
    ! [A_14,A_125] :
      ( r1_tarski(A_14,k3_relat_1(A_125))
      | ~ r1_tarski(A_14,k2_relat_1(A_125))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_22])).

tff(c_66,plain,(
    ! [A_64] :
      ( k2_xboole_0(k1_relat_1(A_64),k2_relat_1(A_64)) = k3_relat_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2277,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2250])).

tff(c_68,plain,(
    ! [A_65,B_67] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_65),k1_relat_1(B_67)),k1_relat_1(k6_subset_1(A_65,B_67)))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2633,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_217),k1_relat_1(B_218)),k1_relat_1(k4_xboole_0(A_217,B_218)))
      | ~ v1_relat_1(B_218)
      | ~ v1_relat_1(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_68])).

tff(c_2690,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2633])).

tff(c_2717,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2277,c_2690])).

tff(c_270,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_257])).

tff(c_2756,plain,(
    k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2717,c_270])).

tff(c_2824,plain,(
    ! [C_29] :
      ( r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_29))
      | ~ r1_tarski(k1_xboole_0,C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_36])).

tff(c_2859,plain,(
    ! [C_223] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_223)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2824])).

tff(c_2885,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2859])).

tff(c_2894,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2885])).

tff(c_10505,plain,(
    ! [A_343,B_344] :
      ( r1_tarski(k3_relat_1(A_343),B_344)
      | ~ r1_tarski(k2_relat_1(A_343),B_344)
      | ~ r1_tarski(k1_relat_1(A_343),B_344)
      | ~ v1_relat_1(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1244])).

tff(c_74,plain,(
    ~ r1_tarski(k3_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10580,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_10505,c_74])).

tff(c_10609,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2894,c_10580])).

tff(c_10625,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_447,c_10609])).

tff(c_10633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2556,c_10625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:48:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.61  
% 7.50/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 7.50/2.61  
% 7.50/2.61  %Foreground sorts:
% 7.50/2.61  
% 7.50/2.61  
% 7.50/2.61  %Background operators:
% 7.50/2.61  
% 7.50/2.61  
% 7.50/2.61  %Foreground operators:
% 7.50/2.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.50/2.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.50/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.50/2.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.50/2.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.50/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/2.61  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.50/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/2.61  tff('#skF_10', type, '#skF_10': $i).
% 7.50/2.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.50/2.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.50/2.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.50/2.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.50/2.61  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.50/2.61  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.50/2.61  tff('#skF_9', type, '#skF_9': $i).
% 7.50/2.61  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.50/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.50/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.50/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.50/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.50/2.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.50/2.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.50/2.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.50/2.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.50/2.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.50/2.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.50/2.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.50/2.61  
% 7.50/2.63  tff(f_160, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.50/2.63  tff(f_85, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.50/2.63  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.50/2.63  tff(f_103, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.50/2.63  tff(f_97, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.50/2.63  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.50/2.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.50/2.63  tff(f_115, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 7.50/2.63  tff(f_143, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 7.50/2.63  tff(f_123, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.50/2.63  tff(f_95, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.50/2.63  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.50/2.63  tff(f_83, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.50/2.63  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.50/2.63  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.50/2.63  tff(f_109, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.50/2.63  tff(f_150, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 7.50/2.63  tff(f_93, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.50/2.63  tff(f_127, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.50/2.63  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.50/2.63  tff(f_134, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 7.50/2.63  tff(c_78, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.50/2.63  tff(c_32, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.50/2.63  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.50/2.63  tff(c_1244, plain, (![A_176, C_177, B_178]: (r1_tarski(k2_xboole_0(A_176, C_177), B_178) | ~r1_tarski(C_177, B_178) | ~r1_tarski(A_176, B_178))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.50/2.63  tff(c_40, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.50/2.63  tff(c_257, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.50/2.63  tff(c_269, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(k2_xboole_0(A_31, B_32), A_31))), inference(resolution, [status(thm)], [c_40, c_257])).
% 7.50/2.63  tff(c_1252, plain, (![B_178, C_177]: (k2_xboole_0(B_178, C_177)=B_178 | ~r1_tarski(C_177, B_178) | ~r1_tarski(B_178, B_178))), inference(resolution, [status(thm)], [c_1244, c_269])).
% 7.50/2.63  tff(c_1280, plain, (![B_179, C_180]: (k2_xboole_0(B_179, C_180)=B_179 | ~r1_tarski(C_180, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1252])).
% 7.50/2.63  tff(c_1330, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(resolution, [status(thm)], [c_32, c_1280])).
% 7.50/2.63  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.50/2.63  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.50/2.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.50/2.63  tff(c_87, plain, (![A_78]: (v1_relat_1(A_78) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.50/2.63  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 7.50/2.63  tff(c_70, plain, (![A_68, B_69]: (r2_hidden('#skF_8'(A_68, B_69), k1_relat_1(B_69)) | ~r2_hidden(A_68, k2_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.50/2.63  tff(c_2235, plain, (![C_210, A_211]: (r2_hidden(k4_tarski(C_210, '#skF_7'(A_211, k1_relat_1(A_211), C_210)), A_211) | ~r2_hidden(C_210, k1_relat_1(A_211)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.50/2.63  tff(c_38, plain, (![A_30]: (r1_xboole_0(A_30, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.50/2.63  tff(c_93, plain, (![B_81, A_82]: (r1_xboole_0(B_81, A_82) | ~r1_xboole_0(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.50/2.63  tff(c_96, plain, (![A_30]: (r1_xboole_0(k1_xboole_0, A_30))), inference(resolution, [status(thm)], [c_38, c_93])).
% 7.50/2.63  tff(c_206, plain, (![A_101, B_102]: (k3_xboole_0(A_101, B_102)=A_101 | ~r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.50/2.63  tff(c_224, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_206])).
% 7.50/2.63  tff(c_343, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, k3_xboole_0(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.50/2.63  tff(c_355, plain, (![A_23, C_116]: (~r1_xboole_0(k1_xboole_0, A_23) | ~r2_hidden(C_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_343])).
% 7.50/2.63  tff(c_361, plain, (![C_116]: (~r2_hidden(C_116, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_355])).
% 7.50/2.63  tff(c_2250, plain, (![C_212]: (~r2_hidden(C_212, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2235, c_361])).
% 7.50/2.63  tff(c_2262, plain, (![A_68]: (~r2_hidden(A_68, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_70, c_2250])).
% 7.50/2.63  tff(c_2314, plain, (![A_213]: (~r2_hidden(A_213, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2262])).
% 7.50/2.63  tff(c_2334, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2314])).
% 7.50/2.63  tff(c_76, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.50/2.63  tff(c_121, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.50/2.63  tff(c_136, plain, (k4_xboole_0('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_121])).
% 7.50/2.63  tff(c_48, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.50/2.63  tff(c_72, plain, (![A_71, B_73]: (r1_tarski(k6_subset_1(k2_relat_1(A_71), k2_relat_1(B_73)), k2_relat_1(k6_subset_1(A_71, B_73))) | ~v1_relat_1(B_73) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.50/2.63  tff(c_2439, plain, (![A_215, B_216]: (r1_tarski(k4_xboole_0(k2_relat_1(A_215), k2_relat_1(B_216)), k2_relat_1(k4_xboole_0(A_215, B_216))) | ~v1_relat_1(B_216) | ~v1_relat_1(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_72])).
% 7.50/2.63  tff(c_2493, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_136, c_2439])).
% 7.50/2.63  tff(c_2519, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2334, c_2493])).
% 7.50/2.63  tff(c_36, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, k2_xboole_0(B_28, C_29)) | ~r1_tarski(k4_xboole_0(A_27, B_28), C_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.50/2.63  tff(c_2536, plain, (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(k2_relat_1('#skF_10'), k1_xboole_0))), inference(resolution, [status(thm)], [c_2519, c_36])).
% 7.50/2.63  tff(c_2556, plain, (r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_2536])).
% 7.50/2.63  tff(c_441, plain, (![A_125]: (k2_xboole_0(k1_relat_1(A_125), k2_relat_1(A_125))=k3_relat_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.50/2.63  tff(c_22, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, k2_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.50/2.63  tff(c_447, plain, (![A_14, A_125]: (r1_tarski(A_14, k3_relat_1(A_125)) | ~r1_tarski(A_14, k2_relat_1(A_125)) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_441, c_22])).
% 7.50/2.63  tff(c_66, plain, (![A_64]: (k2_xboole_0(k1_relat_1(A_64), k2_relat_1(A_64))=k3_relat_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.50/2.63  tff(c_2277, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2250])).
% 7.50/2.63  tff(c_68, plain, (![A_65, B_67]: (r1_tarski(k6_subset_1(k1_relat_1(A_65), k1_relat_1(B_67)), k1_relat_1(k6_subset_1(A_65, B_67))) | ~v1_relat_1(B_67) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.50/2.63  tff(c_2633, plain, (![A_217, B_218]: (r1_tarski(k4_xboole_0(k1_relat_1(A_217), k1_relat_1(B_218)), k1_relat_1(k4_xboole_0(A_217, B_218))) | ~v1_relat_1(B_218) | ~v1_relat_1(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_68])).
% 7.50/2.63  tff(c_2690, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_136, c_2633])).
% 7.50/2.63  tff(c_2717, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2277, c_2690])).
% 7.50/2.63  tff(c_270, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_257])).
% 7.50/2.63  tff(c_2756, plain, (k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2717, c_270])).
% 7.50/2.63  tff(c_2824, plain, (![C_29]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_29)) | ~r1_tarski(k1_xboole_0, C_29))), inference(superposition, [status(thm), theory('equality')], [c_2756, c_36])).
% 7.50/2.63  tff(c_2859, plain, (![C_223]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_223)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2824])).
% 7.50/2.63  tff(c_2885, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_66, c_2859])).
% 7.50/2.63  tff(c_2894, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2885])).
% 7.50/2.63  tff(c_10505, plain, (![A_343, B_344]: (r1_tarski(k3_relat_1(A_343), B_344) | ~r1_tarski(k2_relat_1(A_343), B_344) | ~r1_tarski(k1_relat_1(A_343), B_344) | ~v1_relat_1(A_343))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1244])).
% 7.50/2.63  tff(c_74, plain, (~r1_tarski(k3_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.50/2.63  tff(c_10580, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_10505, c_74])).
% 7.50/2.63  tff(c_10609, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2894, c_10580])).
% 7.50/2.63  tff(c_10625, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_447, c_10609])).
% 7.50/2.63  tff(c_10633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_2556, c_10625])).
% 7.50/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.63  
% 7.50/2.63  Inference rules
% 7.50/2.63  ----------------------
% 7.50/2.63  #Ref     : 1
% 7.50/2.63  #Sup     : 2531
% 7.50/2.63  #Fact    : 0
% 7.50/2.63  #Define  : 0
% 7.50/2.63  #Split   : 3
% 7.50/2.63  #Chain   : 0
% 7.50/2.63  #Close   : 0
% 7.50/2.63  
% 7.50/2.63  Ordering : KBO
% 7.50/2.63  
% 7.50/2.63  Simplification rules
% 7.50/2.63  ----------------------
% 7.50/2.63  #Subsume      : 340
% 7.50/2.63  #Demod        : 1434
% 7.50/2.63  #Tautology    : 1213
% 7.50/2.63  #SimpNegUnit  : 8
% 7.50/2.63  #BackRed      : 34
% 7.50/2.63  
% 7.50/2.63  #Partial instantiations: 0
% 7.50/2.63  #Strategies tried      : 1
% 7.50/2.63  
% 7.50/2.63  Timing (in seconds)
% 7.50/2.63  ----------------------
% 7.50/2.63  Preprocessing        : 0.37
% 7.50/2.63  Parsing              : 0.19
% 7.50/2.63  CNF conversion       : 0.03
% 7.50/2.63  Main loop            : 1.50
% 7.50/2.63  Inferencing          : 0.43
% 7.50/2.63  Reduction            : 0.57
% 7.50/2.63  Demodulation         : 0.44
% 7.50/2.63  BG Simplification    : 0.05
% 7.50/2.63  Subsumption          : 0.33
% 7.50/2.63  Abstraction          : 0.06
% 7.50/2.63  MUC search           : 0.00
% 7.50/2.63  Cooper               : 0.00
% 7.50/2.63  Total                : 1.90
% 7.50/2.63  Index Insertion      : 0.00
% 7.50/2.63  Index Deletion       : 0.00
% 7.50/2.63  Index Matching       : 0.00
% 7.50/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
