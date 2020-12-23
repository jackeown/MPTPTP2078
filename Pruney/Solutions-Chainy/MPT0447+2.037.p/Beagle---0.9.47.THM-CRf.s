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

% Result     : Theorem 9.29s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 155 expanded)
%              Number of leaves         :   48 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  160 ( 267 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_80,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( r1_tarski(C_14,'#skF_3'(A_12,B_13,C_14))
      | k2_xboole_0(A_12,C_14) = B_13
      | ~ r1_tarski(C_14,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9371,plain,(
    ! [B_287,A_288,C_289] :
      ( ~ r1_tarski(B_287,'#skF_3'(A_288,B_287,C_289))
      | k2_xboole_0(A_288,C_289) = B_287
      | ~ r1_tarski(C_289,B_287)
      | ~ r1_tarski(A_288,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9379,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(B_13,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_9371])).

tff(c_9406,plain,(
    ! [A_290,B_291] :
      ( k2_xboole_0(A_290,B_291) = B_291
      | ~ r1_tarski(A_290,B_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9379])).

tff(c_9497,plain,(
    k2_xboole_0('#skF_12','#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_76,c_9406])).

tff(c_1325,plain,(
    ! [A_172,B_173] :
      ( k2_xboole_0(k2_relat_1(A_172),k2_relat_1(B_173)) = k2_relat_1(k2_xboole_0(A_172,B_173))
      | ~ v1_relat_1(B_173)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14877,plain,(
    ! [A_396,B_397] :
      ( r1_tarski(k2_relat_1(A_396),k2_relat_1(k2_xboole_0(A_396,B_397)))
      | ~ v1_relat_1(B_397)
      | ~ v1_relat_1(A_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_30])).

tff(c_14936,plain,
    ( r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_9497,c_14877])).

tff(c_14993,plain,(
    r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_14936])).

tff(c_156,plain,(
    ! [A_100] :
      ( k2_xboole_0(k1_relat_1(A_100),k2_relat_1(A_100)) = k3_relat_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [A_9,A_100] :
      ( r1_tarski(A_9,k3_relat_1(A_100))
      | ~ r1_tarski(A_9,k2_relat_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_68,plain,(
    ! [A_70] :
      ( k2_xboole_0(k1_relat_1(A_70),k2_relat_1(A_70)) = k3_relat_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1181,plain,(
    ! [C_166,A_167] :
      ( r2_hidden(k4_tarski(C_166,'#skF_11'(A_167,k1_relat_1(A_167),C_166)),A_167)
      | ~ r2_hidden(C_166,k1_relat_1(A_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_374,plain,(
    ! [A_127,C_128] :
      ( r2_hidden('#skF_7'(A_127,k3_tarski(A_127),C_128),A_127)
      | ~ r2_hidden(C_128,k3_tarski(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_386,plain,(
    ! [A_129,C_130] :
      ( ~ v1_xboole_0(A_129)
      | ~ r2_hidden(C_130,k3_tarski(A_129)) ) ),
    inference(resolution,[status(thm)],[c_374,c_2])).

tff(c_413,plain,(
    ! [A_132] :
      ( ~ v1_xboole_0(A_132)
      | k3_tarski(A_132) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_386])).

tff(c_421,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_413])).

tff(c_384,plain,(
    ! [A_127,C_128] :
      ( ~ v1_xboole_0(A_127)
      | ~ r2_hidden(C_128,k3_tarski(A_127)) ) ),
    inference(resolution,[status(thm)],[c_374,c_2])).

tff(c_456,plain,(
    ! [C_128] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_128,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_384])).

tff(c_465,plain,(
    ! [C_128] : ~ r2_hidden(C_128,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_456])).

tff(c_1208,plain,(
    ! [C_168] : ~ r2_hidden(C_168,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1181,c_465])).

tff(c_1233,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1208])).

tff(c_422,plain,(
    ! [A_133,C_134,B_135] :
      ( r1_tarski(k2_xboole_0(A_133,C_134),B_135)
      | ~ r1_tarski(C_134,B_135)
      | ~ r1_tarski(A_133,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(k2_xboole_0(A_23,B_24),A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_122])).

tff(c_433,plain,(
    ! [B_135,C_134] :
      ( k2_xboole_0(B_135,C_134) = B_135
      | ~ r1_tarski(C_134,B_135)
      | ~ r1_tarski(B_135,B_135) ) ),
    inference(resolution,[status(thm)],[c_422,c_134])).

tff(c_602,plain,(
    ! [B_143,C_144] :
      ( k2_xboole_0(B_143,C_144) = B_143
      | ~ r1_tarski(C_144,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_433])).

tff(c_644,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(resolution,[status(thm)],[c_24,c_602])).

tff(c_209,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(k4_xboole_0(A_109,B_110),C_111)
      | ~ r1_tarski(A_109,k2_xboole_0(B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_220,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k1_xboole_0
      | ~ r1_tarski(A_109,k2_xboole_0(B_110,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_209,c_135])).

tff(c_779,plain,(
    ! [A_150,B_151] :
      ( k4_xboole_0(A_150,B_151) = k1_xboole_0
      | ~ r1_tarski(A_150,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_220])).

tff(c_823,plain,(
    k4_xboole_0('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_779])).

tff(c_54,plain,(
    ! [A_49,B_50] : k6_subset_1(A_49,B_50) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    ! [A_71,B_73] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_71),k1_relat_1(B_73)),k1_relat_1(k6_subset_1(A_71,B_73)))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3167,plain,(
    ! [A_211,B_212] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_211),k1_relat_1(B_212)),k1_relat_1(k4_xboole_0(A_211,B_212)))
      | ~ v1_relat_1(B_212)
      | ~ v1_relat_1(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_70])).

tff(c_3229,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_3167])).

tff(c_3255,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1233,c_3229])).

tff(c_3348,plain,(
    k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3255,c_135])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,k2_xboole_0(B_21,C_22))
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3386,plain,(
    ! [C_22] :
      ( r1_tarski(k1_relat_1('#skF_12'),k2_xboole_0(k1_relat_1('#skF_13'),C_22))
      | ~ r1_tarski(k1_xboole_0,C_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_28])).

tff(c_3449,plain,(
    ! [C_216] : r1_tarski(k1_relat_1('#skF_12'),k2_xboole_0(k1_relat_1('#skF_13'),C_216)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3386])).

tff(c_3471,plain,
    ( r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3449])).

tff(c_3479,plain,(
    r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3471])).

tff(c_18219,plain,(
    ! [A_445,B_446] :
      ( r1_tarski(k3_relat_1(A_445),B_446)
      | ~ r1_tarski(k2_relat_1(A_445),B_446)
      | ~ r1_tarski(k1_relat_1(A_445),B_446)
      | ~ v1_relat_1(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_422])).

tff(c_74,plain,(
    ~ r1_tarski(k3_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_18299,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_18219,c_74])).

tff(c_18333,plain,(
    ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3479,c_18299])).

tff(c_18343,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_162,c_18333])).

tff(c_18348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14993,c_18343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.29/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.29/3.47  
% 9.29/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.47  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 9.46/3.47  
% 9.46/3.47  %Foreground sorts:
% 9.46/3.47  
% 9.46/3.47  
% 9.46/3.47  %Background operators:
% 9.46/3.47  
% 9.46/3.47  
% 9.46/3.47  %Foreground operators:
% 9.46/3.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.46/3.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.46/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.46/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.46/3.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.46/3.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.46/3.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.46/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.46/3.47  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.46/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.46/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.46/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.46/3.47  tff('#skF_13', type, '#skF_13': $i).
% 9.46/3.47  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 9.46/3.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.46/3.47  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.46/3.47  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 9.46/3.47  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.46/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.46/3.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.46/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.46/3.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.46/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.46/3.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.46/3.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.46/3.47  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.46/3.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.46/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.46/3.47  tff('#skF_12', type, '#skF_12': $i).
% 9.46/3.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.46/3.47  
% 9.46/3.49  tff(f_131, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 9.46/3.49  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.46/3.49  tff(f_63, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 9.46/3.49  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 9.46/3.49  tff(f_75, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.46/3.49  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 9.46/3.49  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.46/3.49  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.46/3.49  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.46/3.49  tff(f_103, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 9.46/3.49  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.46/3.49  tff(f_91, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 9.46/3.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.46/3.49  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 9.46/3.49  tff(f_69, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.46/3.49  tff(f_95, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.46/3.49  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 9.46/3.49  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.46/3.49  tff(c_78, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.46/3.49  tff(c_80, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.46/3.49  tff(c_76, plain, (r1_tarski('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.46/3.49  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.46/3.49  tff(c_20, plain, (![C_14, A_12, B_13]: (r1_tarski(C_14, '#skF_3'(A_12, B_13, C_14)) | k2_xboole_0(A_12, C_14)=B_13 | ~r1_tarski(C_14, B_13) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.46/3.49  tff(c_9371, plain, (![B_287, A_288, C_289]: (~r1_tarski(B_287, '#skF_3'(A_288, B_287, C_289)) | k2_xboole_0(A_288, C_289)=B_287 | ~r1_tarski(C_289, B_287) | ~r1_tarski(A_288, B_287))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.46/3.49  tff(c_9379, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(B_13, B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_9371])).
% 9.46/3.49  tff(c_9406, plain, (![A_290, B_291]: (k2_xboole_0(A_290, B_291)=B_291 | ~r1_tarski(A_290, B_291))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9379])).
% 9.46/3.49  tff(c_9497, plain, (k2_xboole_0('#skF_12', '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_76, c_9406])).
% 9.46/3.49  tff(c_1325, plain, (![A_172, B_173]: (k2_xboole_0(k2_relat_1(A_172), k2_relat_1(B_173))=k2_relat_1(k2_xboole_0(A_172, B_173)) | ~v1_relat_1(B_173) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.49  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.46/3.49  tff(c_14877, plain, (![A_396, B_397]: (r1_tarski(k2_relat_1(A_396), k2_relat_1(k2_xboole_0(A_396, B_397))) | ~v1_relat_1(B_397) | ~v1_relat_1(A_396))), inference(superposition, [status(thm), theory('equality')], [c_1325, c_30])).
% 9.46/3.49  tff(c_14936, plain, (r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_9497, c_14877])).
% 9.46/3.49  tff(c_14993, plain, (r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_14936])).
% 9.46/3.49  tff(c_156, plain, (![A_100]: (k2_xboole_0(k1_relat_1(A_100), k2_relat_1(A_100))=k3_relat_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.46/3.49  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.46/3.49  tff(c_162, plain, (![A_9, A_100]: (r1_tarski(A_9, k3_relat_1(A_100)) | ~r1_tarski(A_9, k2_relat_1(A_100)) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 9.46/3.49  tff(c_68, plain, (![A_70]: (k2_xboole_0(k1_relat_1(A_70), k2_relat_1(A_70))=k3_relat_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.46/3.49  tff(c_24, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.46/3.49  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.46/3.49  tff(c_1181, plain, (![C_166, A_167]: (r2_hidden(k4_tarski(C_166, '#skF_11'(A_167, k1_relat_1(A_167), C_166)), A_167) | ~r2_hidden(C_166, k1_relat_1(A_167)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.46/3.49  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.46/3.49  tff(c_374, plain, (![A_127, C_128]: (r2_hidden('#skF_7'(A_127, k3_tarski(A_127), C_128), A_127) | ~r2_hidden(C_128, k3_tarski(A_127)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.46/3.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.49  tff(c_386, plain, (![A_129, C_130]: (~v1_xboole_0(A_129) | ~r2_hidden(C_130, k3_tarski(A_129)))), inference(resolution, [status(thm)], [c_374, c_2])).
% 9.46/3.49  tff(c_413, plain, (![A_132]: (~v1_xboole_0(A_132) | k3_tarski(A_132)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_386])).
% 9.46/3.49  tff(c_421, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_413])).
% 9.46/3.49  tff(c_384, plain, (![A_127, C_128]: (~v1_xboole_0(A_127) | ~r2_hidden(C_128, k3_tarski(A_127)))), inference(resolution, [status(thm)], [c_374, c_2])).
% 9.46/3.49  tff(c_456, plain, (![C_128]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_421, c_384])).
% 9.46/3.49  tff(c_465, plain, (![C_128]: (~r2_hidden(C_128, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_456])).
% 9.46/3.49  tff(c_1208, plain, (![C_168]: (~r2_hidden(C_168, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1181, c_465])).
% 9.46/3.49  tff(c_1233, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1208])).
% 9.46/3.49  tff(c_422, plain, (![A_133, C_134, B_135]: (r1_tarski(k2_xboole_0(A_133, C_134), B_135) | ~r1_tarski(C_134, B_135) | ~r1_tarski(A_133, B_135))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.49  tff(c_122, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.46/3.49  tff(c_134, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(k2_xboole_0(A_23, B_24), A_23))), inference(resolution, [status(thm)], [c_30, c_122])).
% 9.46/3.49  tff(c_433, plain, (![B_135, C_134]: (k2_xboole_0(B_135, C_134)=B_135 | ~r1_tarski(C_134, B_135) | ~r1_tarski(B_135, B_135))), inference(resolution, [status(thm)], [c_422, c_134])).
% 9.46/3.49  tff(c_602, plain, (![B_143, C_144]: (k2_xboole_0(B_143, C_144)=B_143 | ~r1_tarski(C_144, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_433])).
% 9.46/3.49  tff(c_644, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(resolution, [status(thm)], [c_24, c_602])).
% 9.46/3.49  tff(c_209, plain, (![A_109, B_110, C_111]: (r1_tarski(k4_xboole_0(A_109, B_110), C_111) | ~r1_tarski(A_109, k2_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.46/3.49  tff(c_135, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_122])).
% 9.46/3.49  tff(c_220, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k1_xboole_0 | ~r1_tarski(A_109, k2_xboole_0(B_110, k1_xboole_0)))), inference(resolution, [status(thm)], [c_209, c_135])).
% 9.46/3.49  tff(c_779, plain, (![A_150, B_151]: (k4_xboole_0(A_150, B_151)=k1_xboole_0 | ~r1_tarski(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_644, c_220])).
% 9.46/3.49  tff(c_823, plain, (k4_xboole_0('#skF_12', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_779])).
% 9.46/3.49  tff(c_54, plain, (![A_49, B_50]: (k6_subset_1(A_49, B_50)=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.46/3.49  tff(c_70, plain, (![A_71, B_73]: (r1_tarski(k6_subset_1(k1_relat_1(A_71), k1_relat_1(B_73)), k1_relat_1(k6_subset_1(A_71, B_73))) | ~v1_relat_1(B_73) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.46/3.49  tff(c_3167, plain, (![A_211, B_212]: (r1_tarski(k4_xboole_0(k1_relat_1(A_211), k1_relat_1(B_212)), k1_relat_1(k4_xboole_0(A_211, B_212))) | ~v1_relat_1(B_212) | ~v1_relat_1(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_70])).
% 9.46/3.49  tff(c_3229, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_823, c_3167])).
% 9.46/3.49  tff(c_3255, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1233, c_3229])).
% 9.46/3.49  tff(c_3348, plain, (k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3255, c_135])).
% 9.46/3.49  tff(c_28, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, k2_xboole_0(B_21, C_22)) | ~r1_tarski(k4_xboole_0(A_20, B_21), C_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.46/3.49  tff(c_3386, plain, (![C_22]: (r1_tarski(k1_relat_1('#skF_12'), k2_xboole_0(k1_relat_1('#skF_13'), C_22)) | ~r1_tarski(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_3348, c_28])).
% 9.46/3.49  tff(c_3449, plain, (![C_216]: (r1_tarski(k1_relat_1('#skF_12'), k2_xboole_0(k1_relat_1('#skF_13'), C_216)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3386])).
% 9.46/3.49  tff(c_3471, plain, (r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_68, c_3449])).
% 9.46/3.49  tff(c_3479, plain, (r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3471])).
% 9.46/3.49  tff(c_18219, plain, (![A_445, B_446]: (r1_tarski(k3_relat_1(A_445), B_446) | ~r1_tarski(k2_relat_1(A_445), B_446) | ~r1_tarski(k1_relat_1(A_445), B_446) | ~v1_relat_1(A_445))), inference(superposition, [status(thm), theory('equality')], [c_68, c_422])).
% 9.46/3.49  tff(c_74, plain, (~r1_tarski(k3_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.46/3.49  tff(c_18299, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_18219, c_74])).
% 9.46/3.49  tff(c_18333, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3479, c_18299])).
% 9.46/3.49  tff(c_18343, plain, (~r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_162, c_18333])).
% 9.46/3.49  tff(c_18348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_14993, c_18343])).
% 9.46/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.49  
% 9.46/3.49  Inference rules
% 9.46/3.49  ----------------------
% 9.46/3.49  #Ref     : 0
% 9.46/3.49  #Sup     : 4440
% 9.46/3.49  #Fact    : 0
% 9.46/3.49  #Define  : 0
% 9.46/3.49  #Split   : 13
% 9.46/3.49  #Chain   : 0
% 9.46/3.49  #Close   : 0
% 9.46/3.49  
% 9.46/3.49  Ordering : KBO
% 9.46/3.49  
% 9.46/3.49  Simplification rules
% 9.46/3.49  ----------------------
% 9.46/3.49  #Subsume      : 833
% 9.46/3.49  #Demod        : 4346
% 9.46/3.49  #Tautology    : 2312
% 9.46/3.49  #SimpNegUnit  : 46
% 9.46/3.49  #BackRed      : 45
% 9.46/3.49  
% 9.46/3.49  #Partial instantiations: 0
% 9.46/3.49  #Strategies tried      : 1
% 9.46/3.49  
% 9.46/3.49  Timing (in seconds)
% 9.46/3.49  ----------------------
% 9.46/3.49  Preprocessing        : 0.35
% 9.46/3.49  Parsing              : 0.18
% 9.46/3.49  CNF conversion       : 0.03
% 9.46/3.49  Main loop            : 2.37
% 9.46/3.49  Inferencing          : 0.57
% 9.46/3.49  Reduction            : 0.89
% 9.46/3.49  Demodulation         : 0.69
% 9.46/3.49  BG Simplification    : 0.07
% 9.46/3.49  Subsumption          : 0.70
% 9.46/3.49  Abstraction          : 0.09
% 9.46/3.49  MUC search           : 0.00
% 9.46/3.49  Cooper               : 0.00
% 9.46/3.49  Total                : 2.76
% 9.46/3.49  Index Insertion      : 0.00
% 9.46/3.49  Index Deletion       : 0.00
% 9.46/3.49  Index Matching       : 0.00
% 9.46/3.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
