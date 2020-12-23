%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 16.29s
% Output     : CNFRefutation 16.34s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 222 expanded)
%              Number of leaves         :   54 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 425 expanded)
%              Number of equality atoms :   39 (  87 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_2 > #skF_4 > #skF_15 > #skF_12 > #skF_14 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

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

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_80,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_154,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_123,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_86,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_138,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_172,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_158,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_165,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_90,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_28,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_129,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(A_119,B_120) = k1_xboole_0
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_145,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_129])).

tff(c_92,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2066,plain,(
    ! [A_246,C_247] :
      ( r2_hidden(k4_tarski('#skF_13'(A_246,k2_relat_1(A_246),C_247),C_247),A_246)
      | ~ r2_hidden(C_247,k2_relat_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    ! [A_33] : r2_hidden(A_33,'#skF_4'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_262,plain,(
    ! [C_140,A_141,D_142] :
      ( r2_hidden(C_140,k1_relat_1(A_141))
      | ~ r2_hidden(k4_tarski(C_140,D_142),A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_267,plain,(
    ! [C_140,D_142] : r2_hidden(C_140,k1_relat_1('#skF_4'(k4_tarski(C_140,D_142)))) ),
    inference(resolution,[status(thm)],[c_48,c_262])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_5'(A_51,B_52),B_52)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_274,plain,(
    ! [A_145,B_146,C_147] :
      ( ~ r1_xboole_0(A_145,B_146)
      | ~ r2_hidden(C_147,B_146)
      | ~ r2_hidden(C_147,A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_278,plain,(
    ! [C_148,A_149] :
      ( ~ r2_hidden(C_148,k1_xboole_0)
      | ~ r2_hidden(C_148,A_149) ) ),
    inference(resolution,[status(thm)],[c_32,c_274])).

tff(c_297,plain,(
    ! [A_150,A_151] :
      ( ~ r2_hidden('#skF_5'(A_150,k1_xboole_0),A_151)
      | ~ r2_hidden(A_150,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_278])).

tff(c_308,plain,(
    ! [A_150] : ~ r2_hidden(A_150,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_267,c_297])).

tff(c_2085,plain,(
    ! [C_248] : ~ r2_hidden(C_248,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2066,c_308])).

tff(c_2120,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_2085])).

tff(c_88,plain,(
    r1_tarski('#skF_14','#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_143,plain,(
    k4_xboole_0('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_129])).

tff(c_54,plain,(
    ! [A_58,B_59] : k6_subset_1(A_58,B_59) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_84,plain,(
    ! [A_102,B_104] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_102),k2_relat_1(B_104)),k2_relat_1(k6_subset_1(A_102,B_104)))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2581,plain,(
    ! [A_258,B_259] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_258),k2_relat_1(B_259)),k2_relat_1(k4_xboole_0(A_258,B_259)))
      | ~ v1_relat_1(B_259)
      | ~ v1_relat_1(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_84])).

tff(c_2640,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_15')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2581])).

tff(c_2662,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2120,c_2640])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(B_127,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_2677,plain,
    ( k4_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2662,c_207])).

tff(c_2697,plain,(
    k4_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2677])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3631,plain,(
    ! [C_290,A_291,B_292] :
      ( r1_tarski(C_290,'#skF_3'(A_291,B_292,C_290))
      | k2_xboole_0(A_291,C_290) = B_292
      | ~ r1_tarski(C_290,B_292)
      | ~ r1_tarski(A_291,B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(B_16,'#skF_3'(A_15,B_16,C_17))
      | k2_xboole_0(A_15,C_17) = B_16
      | ~ r1_tarski(C_17,B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3635,plain,(
    ! [A_291,B_292] :
      ( k2_xboole_0(A_291,B_292) = B_292
      | ~ r1_tarski(B_292,B_292)
      | ~ r1_tarski(A_291,B_292) ) ),
    inference(resolution,[status(thm)],[c_3631,c_22])).

tff(c_3690,plain,(
    ! [A_294,B_295] :
      ( k2_xboole_0(A_294,B_295) = B_295
      | ~ r1_tarski(A_294,B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3635])).

tff(c_4264,plain,(
    ! [A_303,B_304] :
      ( k2_xboole_0(A_303,B_304) = B_304
      | k4_xboole_0(A_303,B_304) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_3690])).

tff(c_4313,plain,(
    k2_xboole_0(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')) = k2_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_2697,c_4264])).

tff(c_34,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4463,plain,(
    r1_tarski(k2_relat_1('#skF_14'),k2_relat_1('#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4313,c_34])).

tff(c_349,plain,(
    ! [A_157] :
      ( k2_xboole_0(k1_relat_1(A_157),k2_relat_1(A_157)) = k3_relat_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_355,plain,(
    ! [A_12,A_157] :
      ( r1_tarski(A_12,k3_relat_1(A_157))
      | ~ r1_tarski(A_12,k2_relat_1(A_157))
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_20])).

tff(c_1494,plain,(
    ! [C_227,A_228] :
      ( r2_hidden(k4_tarski(C_227,'#skF_9'(A_228,k1_relat_1(A_228),C_227)),A_228)
      | ~ r2_hidden(C_227,k1_relat_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1513,plain,(
    ! [C_229] : ~ r2_hidden(C_229,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1494,c_308])).

tff(c_1543,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1513])).

tff(c_82,plain,(
    ! [A_99,B_101] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_99),k1_relat_1(B_101)),k1_relat_1(k6_subset_1(A_99,B_101)))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2357,plain,(
    ! [A_253,B_254] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_253),k1_relat_1(B_254)),k1_relat_1(k4_xboole_0(A_253,B_254)))
      | ~ v1_relat_1(B_254)
      | ~ v1_relat_1(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_82])).

tff(c_2413,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_15')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2357])).

tff(c_2434,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1543,c_2413])).

tff(c_2449,plain,
    ( k4_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2434,c_207])).

tff(c_2469,plain,(
    k4_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2449])).

tff(c_4314,plain,(
    k2_xboole_0(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')) = k1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_2469,c_4264])).

tff(c_4571,plain,(
    r1_tarski(k1_relat_1('#skF_14'),k1_relat_1('#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4314,c_34])).

tff(c_361,plain,(
    ! [A_157] :
      ( r1_tarski(k1_relat_1(A_157),k3_relat_1(A_157))
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_34])).

tff(c_766,plain,(
    ! [A_193,C_194,B_195] :
      ( r1_tarski(k2_xboole_0(A_193,C_194),B_195)
      | ~ r1_tarski(C_194,B_195)
      | ~ r1_tarski(A_193,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_208,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(k2_xboole_0(A_24,B_25),A_24) ) ),
    inference(resolution,[status(thm)],[c_34,c_196])).

tff(c_779,plain,(
    ! [B_195,C_194] :
      ( k2_xboole_0(B_195,C_194) = B_195
      | ~ r1_tarski(C_194,B_195)
      | ~ r1_tarski(B_195,B_195) ) ),
    inference(resolution,[status(thm)],[c_766,c_208])).

tff(c_811,plain,(
    ! [B_196,C_197] :
      ( k2_xboole_0(B_196,C_197) = B_196
      | ~ r1_tarski(C_197,B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_779])).

tff(c_1456,plain,(
    ! [A_226] :
      ( k2_xboole_0(k3_relat_1(A_226),k1_relat_1(A_226)) = k3_relat_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_361,c_811])).

tff(c_45457,plain,(
    ! [A_785,A_786] :
      ( r1_tarski(A_785,k3_relat_1(A_786))
      | ~ r1_tarski(A_785,k1_relat_1(A_786))
      | ~ v1_relat_1(A_786) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_20])).

tff(c_80,plain,(
    ! [A_98] :
      ( k2_xboole_0(k1_relat_1(A_98),k2_relat_1(A_98)) = k3_relat_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_14693,plain,(
    ! [A_445,B_446] :
      ( r1_tarski(k3_relat_1(A_445),B_446)
      | ~ r1_tarski(k2_relat_1(A_445),B_446)
      | ~ r1_tarski(k1_relat_1(A_445),B_446)
      | ~ v1_relat_1(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_766])).

tff(c_86,plain,(
    ~ r1_tarski(k3_relat_1('#skF_14'),k3_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_14791,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_14'),k3_relat_1('#skF_15'))
    | ~ r1_tarski(k1_relat_1('#skF_14'),k3_relat_1('#skF_15'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_14693,c_86])).

tff(c_14826,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_14'),k3_relat_1('#skF_15'))
    | ~ r1_tarski(k1_relat_1('#skF_14'),k3_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14791])).

tff(c_14847,plain,(
    ~ r1_tarski(k1_relat_1('#skF_14'),k3_relat_1('#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_14826])).

tff(c_45482,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_14'),k1_relat_1('#skF_15'))
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_45457,c_14847])).

tff(c_45528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4571,c_45482])).

tff(c_45529,plain,(
    ~ r1_tarski(k2_relat_1('#skF_14'),k3_relat_1('#skF_15')) ),
    inference(splitRight,[status(thm)],[c_14826])).

tff(c_45536,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_14'),k2_relat_1('#skF_15'))
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_355,c_45529])).

tff(c_45544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4463,c_45536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.29/8.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.34/8.20  
% 16.34/8.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.34/8.21  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_2 > #skF_4 > #skF_15 > #skF_12 > #skF_14 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 16.34/8.21  
% 16.34/8.21  %Foreground sorts:
% 16.34/8.21  
% 16.34/8.21  
% 16.34/8.21  %Background operators:
% 16.34/8.21  
% 16.34/8.21  
% 16.34/8.21  %Foreground operators:
% 16.34/8.21  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 16.34/8.21  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 16.34/8.21  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.34/8.21  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 16.34/8.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.34/8.21  tff('#skF_4', type, '#skF_4': $i > $i).
% 16.34/8.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.34/8.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.34/8.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.34/8.21  tff('#skF_15', type, '#skF_15': $i).
% 16.34/8.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.34/8.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.34/8.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 16.34/8.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.34/8.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.34/8.21  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 16.34/8.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.34/8.21  tff('#skF_14', type, '#skF_14': $i).
% 16.34/8.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.34/8.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.34/8.21  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 16.34/8.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 16.34/8.21  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 16.34/8.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.34/8.21  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 16.34/8.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.34/8.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.34/8.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.34/8.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.34/8.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.34/8.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.34/8.21  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.34/8.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.34/8.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.34/8.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.34/8.21  
% 16.34/8.23  tff(f_182, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 16.34/8.23  tff(f_80, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.34/8.23  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 16.34/8.23  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.34/8.23  tff(f_154, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 16.34/8.23  tff(f_123, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 16.34/8.23  tff(f_146, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 16.34/8.23  tff(f_136, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 16.34/8.23  tff(f_86, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 16.34/8.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.34/8.23  tff(f_138, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 16.34/8.23  tff(f_172, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 16.34/8.23  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.34/8.23  tff(f_78, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 16.34/8.23  tff(f_88, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.34/8.23  tff(f_158, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 16.34/8.23  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 16.34/8.23  tff(f_165, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 16.34/8.23  tff(f_94, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 16.34/8.23  tff(c_90, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_182])).
% 16.34/8.23  tff(c_28, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.34/8.23  tff(c_129, plain, (![A_119, B_120]: (k4_xboole_0(A_119, B_120)=k1_xboole_0 | ~r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.34/8.23  tff(c_145, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_129])).
% 16.34/8.23  tff(c_92, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_182])).
% 16.34/8.23  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.34/8.23  tff(c_2066, plain, (![A_246, C_247]: (r2_hidden(k4_tarski('#skF_13'(A_246, k2_relat_1(A_246), C_247), C_247), A_246) | ~r2_hidden(C_247, k2_relat_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.34/8.23  tff(c_48, plain, (![A_33]: (r2_hidden(A_33, '#skF_4'(A_33)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.34/8.23  tff(c_262, plain, (![C_140, A_141, D_142]: (r2_hidden(C_140, k1_relat_1(A_141)) | ~r2_hidden(k4_tarski(C_140, D_142), A_141))), inference(cnfTransformation, [status(thm)], [f_146])).
% 16.34/8.23  tff(c_267, plain, (![C_140, D_142]: (r2_hidden(C_140, k1_relat_1('#skF_4'(k4_tarski(C_140, D_142)))))), inference(resolution, [status(thm)], [c_48, c_262])).
% 16.34/8.23  tff(c_52, plain, (![A_51, B_52]: (r2_hidden('#skF_5'(A_51, B_52), B_52) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_136])).
% 16.34/8.23  tff(c_32, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.34/8.23  tff(c_274, plain, (![A_145, B_146, C_147]: (~r1_xboole_0(A_145, B_146) | ~r2_hidden(C_147, B_146) | ~r2_hidden(C_147, A_145))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.34/8.23  tff(c_278, plain, (![C_148, A_149]: (~r2_hidden(C_148, k1_xboole_0) | ~r2_hidden(C_148, A_149))), inference(resolution, [status(thm)], [c_32, c_274])).
% 16.34/8.23  tff(c_297, plain, (![A_150, A_151]: (~r2_hidden('#skF_5'(A_150, k1_xboole_0), A_151) | ~r2_hidden(A_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_278])).
% 16.34/8.23  tff(c_308, plain, (![A_150]: (~r2_hidden(A_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_267, c_297])).
% 16.34/8.23  tff(c_2085, plain, (![C_248]: (~r2_hidden(C_248, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2066, c_308])).
% 16.34/8.23  tff(c_2120, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_2085])).
% 16.34/8.23  tff(c_88, plain, (r1_tarski('#skF_14', '#skF_15')), inference(cnfTransformation, [status(thm)], [f_182])).
% 16.34/8.23  tff(c_143, plain, (k4_xboole_0('#skF_14', '#skF_15')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_129])).
% 16.34/8.23  tff(c_54, plain, (![A_58, B_59]: (k6_subset_1(A_58, B_59)=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_138])).
% 16.34/8.23  tff(c_84, plain, (![A_102, B_104]: (r1_tarski(k6_subset_1(k2_relat_1(A_102), k2_relat_1(B_104)), k2_relat_1(k6_subset_1(A_102, B_104))) | ~v1_relat_1(B_104) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_172])).
% 16.34/8.23  tff(c_2581, plain, (![A_258, B_259]: (r1_tarski(k4_xboole_0(k2_relat_1(A_258), k2_relat_1(B_259)), k2_relat_1(k4_xboole_0(A_258, B_259))) | ~v1_relat_1(B_259) | ~v1_relat_1(A_258))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_84])).
% 16.34/8.23  tff(c_2640, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_15') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_143, c_2581])).
% 16.34/8.23  tff(c_2662, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2120, c_2640])).
% 16.34/8.23  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.34/8.23  tff(c_196, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(B_127, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.34/8.23  tff(c_207, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_196])).
% 16.34/8.23  tff(c_2677, plain, (k4_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2662, c_207])).
% 16.34/8.23  tff(c_2697, plain, (k4_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2677])).
% 16.34/8.23  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.34/8.23  tff(c_3631, plain, (![C_290, A_291, B_292]: (r1_tarski(C_290, '#skF_3'(A_291, B_292, C_290)) | k2_xboole_0(A_291, C_290)=B_292 | ~r1_tarski(C_290, B_292) | ~r1_tarski(A_291, B_292))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.34/8.23  tff(c_22, plain, (![B_16, A_15, C_17]: (~r1_tarski(B_16, '#skF_3'(A_15, B_16, C_17)) | k2_xboole_0(A_15, C_17)=B_16 | ~r1_tarski(C_17, B_16) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.34/8.23  tff(c_3635, plain, (![A_291, B_292]: (k2_xboole_0(A_291, B_292)=B_292 | ~r1_tarski(B_292, B_292) | ~r1_tarski(A_291, B_292))), inference(resolution, [status(thm)], [c_3631, c_22])).
% 16.34/8.23  tff(c_3690, plain, (![A_294, B_295]: (k2_xboole_0(A_294, B_295)=B_295 | ~r1_tarski(A_294, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3635])).
% 16.34/8.23  tff(c_4264, plain, (![A_303, B_304]: (k2_xboole_0(A_303, B_304)=B_304 | k4_xboole_0(A_303, B_304)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3690])).
% 16.34/8.23  tff(c_4313, plain, (k2_xboole_0(k2_relat_1('#skF_14'), k2_relat_1('#skF_15'))=k2_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_2697, c_4264])).
% 16.34/8.23  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.34/8.23  tff(c_4463, plain, (r1_tarski(k2_relat_1('#skF_14'), k2_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_4313, c_34])).
% 16.34/8.23  tff(c_349, plain, (![A_157]: (k2_xboole_0(k1_relat_1(A_157), k2_relat_1(A_157))=k3_relat_1(A_157) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_158])).
% 16.34/8.23  tff(c_20, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.34/8.23  tff(c_355, plain, (![A_12, A_157]: (r1_tarski(A_12, k3_relat_1(A_157)) | ~r1_tarski(A_12, k2_relat_1(A_157)) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_349, c_20])).
% 16.34/8.23  tff(c_1494, plain, (![C_227, A_228]: (r2_hidden(k4_tarski(C_227, '#skF_9'(A_228, k1_relat_1(A_228), C_227)), A_228) | ~r2_hidden(C_227, k1_relat_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 16.34/8.23  tff(c_1513, plain, (![C_229]: (~r2_hidden(C_229, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1494, c_308])).
% 16.34/8.23  tff(c_1543, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1513])).
% 16.34/8.23  tff(c_82, plain, (![A_99, B_101]: (r1_tarski(k6_subset_1(k1_relat_1(A_99), k1_relat_1(B_101)), k1_relat_1(k6_subset_1(A_99, B_101))) | ~v1_relat_1(B_101) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_165])).
% 16.34/8.23  tff(c_2357, plain, (![A_253, B_254]: (r1_tarski(k4_xboole_0(k1_relat_1(A_253), k1_relat_1(B_254)), k1_relat_1(k4_xboole_0(A_253, B_254))) | ~v1_relat_1(B_254) | ~v1_relat_1(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_82])).
% 16.34/8.23  tff(c_2413, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_15') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_143, c_2357])).
% 16.34/8.23  tff(c_2434, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1543, c_2413])).
% 16.34/8.23  tff(c_2449, plain, (k4_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2434, c_207])).
% 16.34/8.23  tff(c_2469, plain, (k4_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2449])).
% 16.34/8.23  tff(c_4314, plain, (k2_xboole_0(k1_relat_1('#skF_14'), k1_relat_1('#skF_15'))=k1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_2469, c_4264])).
% 16.34/8.23  tff(c_4571, plain, (r1_tarski(k1_relat_1('#skF_14'), k1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_4314, c_34])).
% 16.34/8.23  tff(c_361, plain, (![A_157]: (r1_tarski(k1_relat_1(A_157), k3_relat_1(A_157)) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_349, c_34])).
% 16.34/8.23  tff(c_766, plain, (![A_193, C_194, B_195]: (r1_tarski(k2_xboole_0(A_193, C_194), B_195) | ~r1_tarski(C_194, B_195) | ~r1_tarski(A_193, B_195))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.34/8.23  tff(c_208, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(k2_xboole_0(A_24, B_25), A_24))), inference(resolution, [status(thm)], [c_34, c_196])).
% 16.34/8.23  tff(c_779, plain, (![B_195, C_194]: (k2_xboole_0(B_195, C_194)=B_195 | ~r1_tarski(C_194, B_195) | ~r1_tarski(B_195, B_195))), inference(resolution, [status(thm)], [c_766, c_208])).
% 16.34/8.23  tff(c_811, plain, (![B_196, C_197]: (k2_xboole_0(B_196, C_197)=B_196 | ~r1_tarski(C_197, B_196))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_779])).
% 16.34/8.23  tff(c_1456, plain, (![A_226]: (k2_xboole_0(k3_relat_1(A_226), k1_relat_1(A_226))=k3_relat_1(A_226) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_361, c_811])).
% 16.34/8.23  tff(c_45457, plain, (![A_785, A_786]: (r1_tarski(A_785, k3_relat_1(A_786)) | ~r1_tarski(A_785, k1_relat_1(A_786)) | ~v1_relat_1(A_786))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_20])).
% 16.34/8.23  tff(c_80, plain, (![A_98]: (k2_xboole_0(k1_relat_1(A_98), k2_relat_1(A_98))=k3_relat_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_158])).
% 16.34/8.23  tff(c_14693, plain, (![A_445, B_446]: (r1_tarski(k3_relat_1(A_445), B_446) | ~r1_tarski(k2_relat_1(A_445), B_446) | ~r1_tarski(k1_relat_1(A_445), B_446) | ~v1_relat_1(A_445))), inference(superposition, [status(thm), theory('equality')], [c_80, c_766])).
% 16.34/8.23  tff(c_86, plain, (~r1_tarski(k3_relat_1('#skF_14'), k3_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 16.34/8.23  tff(c_14791, plain, (~r1_tarski(k2_relat_1('#skF_14'), k3_relat_1('#skF_15')) | ~r1_tarski(k1_relat_1('#skF_14'), k3_relat_1('#skF_15')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_14693, c_86])).
% 16.34/8.23  tff(c_14826, plain, (~r1_tarski(k2_relat_1('#skF_14'), k3_relat_1('#skF_15')) | ~r1_tarski(k1_relat_1('#skF_14'), k3_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14791])).
% 16.34/8.23  tff(c_14847, plain, (~r1_tarski(k1_relat_1('#skF_14'), k3_relat_1('#skF_15'))), inference(splitLeft, [status(thm)], [c_14826])).
% 16.34/8.23  tff(c_45482, plain, (~r1_tarski(k1_relat_1('#skF_14'), k1_relat_1('#skF_15')) | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_45457, c_14847])).
% 16.34/8.23  tff(c_45528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_4571, c_45482])).
% 16.34/8.23  tff(c_45529, plain, (~r1_tarski(k2_relat_1('#skF_14'), k3_relat_1('#skF_15'))), inference(splitRight, [status(thm)], [c_14826])).
% 16.34/8.23  tff(c_45536, plain, (~r1_tarski(k2_relat_1('#skF_14'), k2_relat_1('#skF_15')) | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_355, c_45529])).
% 16.34/8.23  tff(c_45544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_4463, c_45536])).
% 16.34/8.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.34/8.23  
% 16.34/8.23  Inference rules
% 16.34/8.23  ----------------------
% 16.34/8.23  #Ref     : 0
% 16.34/8.23  #Sup     : 11408
% 16.34/8.23  #Fact    : 0
% 16.34/8.23  #Define  : 0
% 16.34/8.23  #Split   : 21
% 16.34/8.23  #Chain   : 0
% 16.34/8.23  #Close   : 0
% 16.34/8.23  
% 16.34/8.23  Ordering : KBO
% 16.34/8.23  
% 16.34/8.23  Simplification rules
% 16.34/8.23  ----------------------
% 16.34/8.23  #Subsume      : 2902
% 16.34/8.23  #Demod        : 7861
% 16.34/8.23  #Tautology    : 4691
% 16.34/8.23  #SimpNegUnit  : 17
% 16.34/8.23  #BackRed      : 6
% 16.34/8.23  
% 16.34/8.23  #Partial instantiations: 0
% 16.34/8.23  #Strategies tried      : 1
% 16.34/8.23  
% 16.34/8.23  Timing (in seconds)
% 16.34/8.23  ----------------------
% 16.34/8.23  Preprocessing        : 0.36
% 16.34/8.23  Parsing              : 0.18
% 16.34/8.23  CNF conversion       : 0.03
% 16.34/8.23  Main loop            : 7.09
% 16.34/8.23  Inferencing          : 1.14
% 16.34/8.23  Reduction            : 3.19
% 16.34/8.23  Demodulation         : 2.54
% 16.34/8.23  BG Simplification    : 0.12
% 16.34/8.23  Subsumption          : 2.29
% 16.34/8.23  Abstraction          : 0.16
% 16.34/8.23  MUC search           : 0.00
% 16.34/8.23  Cooper               : 0.00
% 16.34/8.23  Total                : 7.48
% 16.34/8.23  Index Insertion      : 0.00
% 16.34/8.23  Index Deletion       : 0.00
% 16.34/8.23  Index Matching       : 0.00
% 16.34/8.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
