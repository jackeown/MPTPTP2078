%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.76s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 314 expanded)
%              Number of leaves         :   54 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  186 ( 512 expanded)
%              Number of equality atoms :   47 ( 146 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_107,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_143,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(c_123,plain,(
    ! [A_102,B_103] : r1_tarski(k4_xboole_0(A_102,B_103),A_102) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_28])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_88,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_78,plain,(
    ! [A_88] :
      ( k2_xboole_0(k1_relat_1(A_88),k2_relat_1(A_88)) = k3_relat_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_160,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k1_xboole_0
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_177,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_160])).

tff(c_304,plain,(
    ! [A_127,B_128] : k4_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = k3_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_329,plain,(
    ! [A_32,B_33] : k3_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_304])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_539,plain,(
    ! [A_140,B_141,C_142] :
      ( ~ r1_xboole_0(A_140,B_141)
      | ~ r2_hidden(C_142,k3_xboole_0(A_140,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_610,plain,(
    ! [A_146,B_147] :
      ( ~ r1_xboole_0(A_146,B_147)
      | k3_xboole_0(A_146,B_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_539])).

tff(c_648,plain,(
    ! [A_150,B_151] :
      ( k3_xboole_0(A_150,B_151) = k1_xboole_0
      | k4_xboole_0(A_150,B_151) != A_150 ) ),
    inference(resolution,[status(thm)],[c_40,c_610])).

tff(c_666,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0
      | k1_xboole_0 != A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_648])).

tff(c_679,plain,(
    ! [A_32] :
      ( k4_xboole_0(A_32,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_666])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1659,plain,(
    ! [A_195,B_196,C_197] :
      ( r1_tarski(A_195,k2_xboole_0(B_196,C_197))
      | ~ r1_tarski(k4_xboole_0(A_195,B_196),C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1987,plain,(
    ! [A_206,B_207] : r1_tarski(A_206,k2_xboole_0(B_207,k4_xboole_0(A_206,B_207))) ),
    inference(resolution,[status(thm)],[c_14,c_1659])).

tff(c_2022,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | k1_xboole_0 != A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_1987])).

tff(c_2062,plain,(
    ! [A_208] :
      ( r1_tarski(A_208,k1_xboole_0)
      | k1_xboole_0 != A_208 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2022])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1204,plain,(
    ! [A_174,C_175,B_176] :
      ( r1_tarski(A_174,C_175)
      | ~ r1_tarski(B_176,C_175)
      | ~ r1_tarski(A_174,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1228,plain,(
    ! [A_174,A_20] :
      ( r1_tarski(A_174,A_20)
      | ~ r1_tarski(A_174,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_1204])).

tff(c_2159,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(resolution,[status(thm)],[c_2062,c_1228])).

tff(c_4860,plain,(
    ! [C_294,A_295] :
      ( r2_hidden(k4_tarski(C_294,'#skF_6'(A_295,k1_relat_1(A_295),C_294)),A_295)
      | ~ r2_hidden(C_294,k1_relat_1(A_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_317,plain,(
    ! [B_128] : k3_xboole_0(k1_xboole_0,B_128) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_128])).

tff(c_548,plain,(
    ! [B_128,C_142] :
      ( ~ r1_xboole_0(k1_xboole_0,B_128)
      | ~ r2_hidden(C_142,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_539])).

tff(c_602,plain,(
    ! [C_142] : ~ r2_hidden(C_142,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_4889,plain,(
    ! [C_296] : ~ r2_hidden(C_296,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4860,c_602])).

tff(c_4904,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_4889])).

tff(c_86,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_178,plain,(
    k4_xboole_0('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_160])).

tff(c_50,plain,(
    ! [A_46,B_47] : k6_subset_1(A_46,B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_80,plain,(
    ! [A_89,B_91] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_89),k1_relat_1(B_91)),k1_relat_1(k6_subset_1(A_89,B_91)))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4929,plain,(
    ! [A_297,B_298] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_297),k1_relat_1(B_298)),k1_relat_1(k4_xboole_0(A_297,B_298)))
      | ~ v1_relat_1(B_298)
      | ~ v1_relat_1(A_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_80])).

tff(c_5009,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_4929])).

tff(c_5039,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4904,c_5009])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7761,plain,
    ( k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12'))) ),
    inference(resolution,[status(thm)],[c_5039,c_10])).

tff(c_7781,plain,(
    k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_7761])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,k2_xboole_0(B_28,C_29))
      | ~ r1_tarski(k4_xboole_0(A_27,B_28),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8074,plain,(
    ! [C_29] :
      ( r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_29))
      | ~ r1_tarski(k1_xboole_0,C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7781,c_32])).

tff(c_9704,plain,(
    ! [C_406] : r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_406)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_8074])).

tff(c_9738,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_9704])).

tff(c_9754,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_9738])).

tff(c_2080,plain,(
    ! [A_208,A_20] :
      ( r1_tarski(A_208,A_20)
      | k1_xboole_0 != A_208 ) ),
    inference(resolution,[status(thm)],[c_2062,c_1228])).

tff(c_42,plain,(
    ! [A_36,C_38,B_37] :
      ( r1_tarski(k2_xboole_0(A_36,C_38),B_37)
      | ~ r1_tarski(C_38,B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_554,plain,(
    ! [B_143,A_144] :
      ( B_143 = A_144
      | ~ r1_tarski(B_143,A_144)
      | ~ r1_tarski(A_144,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6040,plain,(
    ! [A_347,B_348] :
      ( k2_xboole_0(A_347,B_348) = A_347
      | ~ r1_tarski(k2_xboole_0(A_347,B_348),A_347) ) ),
    inference(resolution,[status(thm)],[c_36,c_554])).

tff(c_6048,plain,(
    ! [B_37,C_38] :
      ( k2_xboole_0(B_37,C_38) = B_37
      | ~ r1_tarski(C_38,B_37)
      | ~ r1_tarski(B_37,B_37) ) ),
    inference(resolution,[status(thm)],[c_42,c_6040])).

tff(c_6092,plain,(
    ! [B_349,C_350] :
      ( k2_xboole_0(B_349,C_350) = B_349
      | ~ r1_tarski(C_350,B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6048])).

tff(c_7799,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(resolution,[status(thm)],[c_2080,c_6092])).

tff(c_3799,plain,(
    ! [A_249,C_250] :
      ( r2_hidden(k4_tarski('#skF_10'(A_249,k2_relat_1(A_249),C_250),C_250),A_249)
      | ~ r2_hidden(C_250,k2_relat_1(A_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3828,plain,(
    ! [C_251] : ~ r2_hidden(C_251,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3799,c_602])).

tff(c_3838,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_3828])).

tff(c_82,plain,(
    ! [A_92,B_94] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_92),k2_relat_1(B_94)),k2_relat_1(k6_subset_1(A_92,B_94)))
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5290,plain,(
    ! [A_307,B_308] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_307),k2_relat_1(B_308)),k2_relat_1(k4_xboole_0(A_307,B_308)))
      | ~ v1_relat_1(B_308)
      | ~ v1_relat_1(A_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_82])).

tff(c_5370,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_5290])).

tff(c_5400,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_3838,c_5370])).

tff(c_5949,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5400,c_32])).

tff(c_8851,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7799,c_5949])).

tff(c_6082,plain,(
    ! [B_37,C_38] :
      ( k2_xboole_0(B_37,C_38) = B_37
      | ~ r1_tarski(C_38,B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6048])).

tff(c_8870,plain,(
    k2_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_11')) = k2_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_8851,c_6082])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1581,plain,(
    ! [A_192,A_193,B_194] :
      ( r1_tarski(A_192,A_193)
      | ~ r1_tarski(A_192,k4_xboole_0(A_193,B_194)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1204])).

tff(c_3652,plain,(
    ! [A_246,B_247,B_248] : r1_tarski(k4_xboole_0(k4_xboole_0(A_246,B_247),B_248),A_246) ),
    inference(resolution,[status(thm)],[c_26,c_1581])).

tff(c_4771,plain,(
    ! [A_291,B_292,B_293] : r1_tarski(k4_xboole_0(A_291,B_292),k2_xboole_0(B_293,A_291)) ),
    inference(resolution,[status(thm)],[c_3652,c_32])).

tff(c_4842,plain,(
    ! [A_291,B_292,B_293] : r1_tarski(A_291,k2_xboole_0(B_292,k2_xboole_0(B_293,A_291))) ),
    inference(resolution,[status(thm)],[c_4771,c_32])).

tff(c_10360,plain,(
    ! [B_414] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(B_414,k2_relat_1('#skF_12'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8870,c_4842])).

tff(c_10384,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10360])).

tff(c_10396,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10384])).

tff(c_3279,plain,(
    ! [A_233,C_234,B_235] :
      ( r1_tarski(k2_xboole_0(A_233,C_234),B_235)
      | ~ r1_tarski(C_234,B_235)
      | ~ r1_tarski(A_233,B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28568,plain,(
    ! [A_654,B_655] :
      ( r1_tarski(k3_relat_1(A_654),B_655)
      | ~ r1_tarski(k2_relat_1(A_654),B_655)
      | ~ r1_tarski(k1_relat_1(A_654),B_655)
      | ~ v1_relat_1(A_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3279])).

tff(c_84,plain,(
    ~ r1_tarski(k3_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_28655,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_28568,c_84])).

tff(c_28691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9754,c_10396,c_28655])).

tff(c_28693,plain,(
    ! [B_656] : ~ r1_xboole_0(k1_xboole_0,B_656) ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_28697,plain,(
    ! [B_35] : k4_xboole_0(k1_xboole_0,B_35) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_28693])).

tff(c_28701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_28697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.62/4.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/4.99  
% 11.62/4.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/4.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 11.62/4.99  
% 11.62/4.99  %Foreground sorts:
% 11.62/4.99  
% 11.62/4.99  
% 11.62/4.99  %Background operators:
% 11.62/4.99  
% 11.62/4.99  
% 11.62/4.99  %Foreground operators:
% 11.62/4.99  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.62/4.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.62/4.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.62/4.99  tff('#skF_11', type, '#skF_11': $i).
% 11.62/4.99  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.62/4.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.62/4.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.62/4.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.62/4.99  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 11.62/4.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.62/4.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.62/4.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.62/4.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.62/4.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.62/4.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.62/4.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.62/4.99  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.62/4.99  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 11.62/4.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.62/4.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.62/4.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.62/4.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.62/4.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.62/4.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.62/4.99  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 11.62/4.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.62/4.99  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 11.62/4.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.62/4.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.62/4.99  tff('#skF_12', type, '#skF_12': $i).
% 11.62/4.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.62/4.99  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 11.62/4.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.62/4.99  
% 11.76/5.01  tff(f_73, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.76/5.01  tff(f_77, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 11.76/5.01  tff(f_93, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.76/5.01  tff(f_153, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 11.76/5.01  tff(f_129, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 11.76/5.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.76/5.01  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.76/5.01  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.76/5.01  tff(f_87, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.76/5.01  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.76/5.01  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.76/5.01  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.76/5.01  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.76/5.01  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.76/5.01  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.76/5.01  tff(f_117, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 11.76/5.01  tff(f_107, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.76/5.01  tff(f_136, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 11.76/5.01  tff(f_99, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.76/5.01  tff(f_125, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 11.76/5.01  tff(f_143, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 11.76/5.01  tff(c_123, plain, (![A_102, B_103]: (r1_tarski(k4_xboole_0(A_102, B_103), A_102))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.76/5.01  tff(c_28, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.76/5.01  tff(c_128, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_28])).
% 11.76/5.01  tff(c_40, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.76/5.01  tff(c_90, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.76/5.01  tff(c_88, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.76/5.01  tff(c_78, plain, (![A_88]: (k2_xboole_0(k1_relat_1(A_88), k2_relat_1(A_88))=k3_relat_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.76/5.01  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.76/5.01  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.76/5.01  tff(c_160, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k1_xboole_0 | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.76/5.01  tff(c_177, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_160])).
% 11.76/5.01  tff(c_304, plain, (![A_127, B_128]: (k4_xboole_0(A_127, k4_xboole_0(A_127, B_128))=k3_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.76/5.01  tff(c_329, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k4_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_177, c_304])).
% 11.76/5.01  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.76/5.01  tff(c_539, plain, (![A_140, B_141, C_142]: (~r1_xboole_0(A_140, B_141) | ~r2_hidden(C_142, k3_xboole_0(A_140, B_141)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.76/5.01  tff(c_610, plain, (![A_146, B_147]: (~r1_xboole_0(A_146, B_147) | k3_xboole_0(A_146, B_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_539])).
% 11.76/5.01  tff(c_648, plain, (![A_150, B_151]: (k3_xboole_0(A_150, B_151)=k1_xboole_0 | k4_xboole_0(A_150, B_151)!=A_150)), inference(resolution, [status(thm)], [c_40, c_610])).
% 11.76/5.01  tff(c_666, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0 | k1_xboole_0!=A_32)), inference(superposition, [status(thm), theory('equality')], [c_177, c_648])).
% 11.76/5.01  tff(c_679, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_666])).
% 11.76/5.01  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.76/5.01  tff(c_1659, plain, (![A_195, B_196, C_197]: (r1_tarski(A_195, k2_xboole_0(B_196, C_197)) | ~r1_tarski(k4_xboole_0(A_195, B_196), C_197))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.76/5.01  tff(c_1987, plain, (![A_206, B_207]: (r1_tarski(A_206, k2_xboole_0(B_207, k4_xboole_0(A_206, B_207))))), inference(resolution, [status(thm)], [c_14, c_1659])).
% 11.76/5.01  tff(c_2022, plain, (![A_32]: (r1_tarski(A_32, k2_xboole_0(k1_xboole_0, k1_xboole_0)) | k1_xboole_0!=A_32)), inference(superposition, [status(thm), theory('equality')], [c_679, c_1987])).
% 11.76/5.01  tff(c_2062, plain, (![A_208]: (r1_tarski(A_208, k1_xboole_0) | k1_xboole_0!=A_208)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2022])).
% 11.76/5.01  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.76/5.01  tff(c_1204, plain, (![A_174, C_175, B_176]: (r1_tarski(A_174, C_175) | ~r1_tarski(B_176, C_175) | ~r1_tarski(A_174, B_176))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/5.01  tff(c_1228, plain, (![A_174, A_20]: (r1_tarski(A_174, A_20) | ~r1_tarski(A_174, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_1204])).
% 11.76/5.01  tff(c_2159, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(resolution, [status(thm)], [c_2062, c_1228])).
% 11.76/5.01  tff(c_4860, plain, (![C_294, A_295]: (r2_hidden(k4_tarski(C_294, '#skF_6'(A_295, k1_relat_1(A_295), C_294)), A_295) | ~r2_hidden(C_294, k1_relat_1(A_295)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.76/5.01  tff(c_317, plain, (![B_128]: (k3_xboole_0(k1_xboole_0, B_128)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_304, c_128])).
% 11.76/5.01  tff(c_548, plain, (![B_128, C_142]: (~r1_xboole_0(k1_xboole_0, B_128) | ~r2_hidden(C_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_317, c_539])).
% 11.76/5.01  tff(c_602, plain, (![C_142]: (~r2_hidden(C_142, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_548])).
% 11.76/5.01  tff(c_4889, plain, (![C_296]: (~r2_hidden(C_296, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4860, c_602])).
% 11.76/5.01  tff(c_4904, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_4889])).
% 11.76/5.01  tff(c_86, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.76/5.01  tff(c_178, plain, (k4_xboole_0('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_160])).
% 11.76/5.01  tff(c_50, plain, (![A_46, B_47]: (k6_subset_1(A_46, B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.76/5.01  tff(c_80, plain, (![A_89, B_91]: (r1_tarski(k6_subset_1(k1_relat_1(A_89), k1_relat_1(B_91)), k1_relat_1(k6_subset_1(A_89, B_91))) | ~v1_relat_1(B_91) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.76/5.01  tff(c_4929, plain, (![A_297, B_298]: (r1_tarski(k4_xboole_0(k1_relat_1(A_297), k1_relat_1(B_298)), k1_relat_1(k4_xboole_0(A_297, B_298))) | ~v1_relat_1(B_298) | ~v1_relat_1(A_297))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_80])).
% 11.76/5.01  tff(c_5009, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_178, c_4929])).
% 11.76/5.01  tff(c_5039, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4904, c_5009])).
% 11.76/5.01  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.76/5.01  tff(c_7761, plain, (k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_5039, c_10])).
% 11.76/5.01  tff(c_7781, plain, (k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_7761])).
% 11.76/5.01  tff(c_32, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, k2_xboole_0(B_28, C_29)) | ~r1_tarski(k4_xboole_0(A_27, B_28), C_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.76/5.01  tff(c_8074, plain, (![C_29]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_29)) | ~r1_tarski(k1_xboole_0, C_29))), inference(superposition, [status(thm), theory('equality')], [c_7781, c_32])).
% 11.76/5.01  tff(c_9704, plain, (![C_406]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_406)))), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_8074])).
% 11.76/5.01  tff(c_9738, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_78, c_9704])).
% 11.76/5.01  tff(c_9754, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_9738])).
% 11.76/5.01  tff(c_2080, plain, (![A_208, A_20]: (r1_tarski(A_208, A_20) | k1_xboole_0!=A_208)), inference(resolution, [status(thm)], [c_2062, c_1228])).
% 11.76/5.01  tff(c_42, plain, (![A_36, C_38, B_37]: (r1_tarski(k2_xboole_0(A_36, C_38), B_37) | ~r1_tarski(C_38, B_37) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.76/5.01  tff(c_554, plain, (![B_143, A_144]: (B_143=A_144 | ~r1_tarski(B_143, A_144) | ~r1_tarski(A_144, B_143))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.76/5.01  tff(c_6040, plain, (![A_347, B_348]: (k2_xboole_0(A_347, B_348)=A_347 | ~r1_tarski(k2_xboole_0(A_347, B_348), A_347))), inference(resolution, [status(thm)], [c_36, c_554])).
% 11.76/5.01  tff(c_6048, plain, (![B_37, C_38]: (k2_xboole_0(B_37, C_38)=B_37 | ~r1_tarski(C_38, B_37) | ~r1_tarski(B_37, B_37))), inference(resolution, [status(thm)], [c_42, c_6040])).
% 11.76/5.01  tff(c_6092, plain, (![B_349, C_350]: (k2_xboole_0(B_349, C_350)=B_349 | ~r1_tarski(C_350, B_349))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6048])).
% 11.76/5.01  tff(c_7799, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(resolution, [status(thm)], [c_2080, c_6092])).
% 11.76/5.01  tff(c_3799, plain, (![A_249, C_250]: (r2_hidden(k4_tarski('#skF_10'(A_249, k2_relat_1(A_249), C_250), C_250), A_249) | ~r2_hidden(C_250, k2_relat_1(A_249)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.76/5.01  tff(c_3828, plain, (![C_251]: (~r2_hidden(C_251, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3799, c_602])).
% 11.76/5.01  tff(c_3838, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_3828])).
% 11.76/5.01  tff(c_82, plain, (![A_92, B_94]: (r1_tarski(k6_subset_1(k2_relat_1(A_92), k2_relat_1(B_94)), k2_relat_1(k6_subset_1(A_92, B_94))) | ~v1_relat_1(B_94) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.76/5.01  tff(c_5290, plain, (![A_307, B_308]: (r1_tarski(k4_xboole_0(k2_relat_1(A_307), k2_relat_1(B_308)), k2_relat_1(k4_xboole_0(A_307, B_308))) | ~v1_relat_1(B_308) | ~v1_relat_1(A_307))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_82])).
% 11.76/5.01  tff(c_5370, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_178, c_5290])).
% 11.76/5.01  tff(c_5400, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_11'), k2_relat_1('#skF_12')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_3838, c_5370])).
% 11.76/5.01  tff(c_5949, plain, (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), k1_xboole_0))), inference(resolution, [status(thm)], [c_5400, c_32])).
% 11.76/5.01  tff(c_8851, plain, (r1_tarski(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_7799, c_5949])).
% 11.76/5.01  tff(c_6082, plain, (![B_37, C_38]: (k2_xboole_0(B_37, C_38)=B_37 | ~r1_tarski(C_38, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6048])).
% 11.76/5.01  tff(c_8870, plain, (k2_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_11'))=k2_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_8851, c_6082])).
% 11.76/5.01  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.76/5.01  tff(c_1581, plain, (![A_192, A_193, B_194]: (r1_tarski(A_192, A_193) | ~r1_tarski(A_192, k4_xboole_0(A_193, B_194)))), inference(resolution, [status(thm)], [c_26, c_1204])).
% 11.76/5.01  tff(c_3652, plain, (![A_246, B_247, B_248]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_246, B_247), B_248), A_246))), inference(resolution, [status(thm)], [c_26, c_1581])).
% 11.76/5.01  tff(c_4771, plain, (![A_291, B_292, B_293]: (r1_tarski(k4_xboole_0(A_291, B_292), k2_xboole_0(B_293, A_291)))), inference(resolution, [status(thm)], [c_3652, c_32])).
% 11.76/5.01  tff(c_4842, plain, (![A_291, B_292, B_293]: (r1_tarski(A_291, k2_xboole_0(B_292, k2_xboole_0(B_293, A_291))))), inference(resolution, [status(thm)], [c_4771, c_32])).
% 11.76/5.01  tff(c_10360, plain, (![B_414]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(B_414, k2_relat_1('#skF_12'))))), inference(superposition, [status(thm), theory('equality')], [c_8870, c_4842])).
% 11.76/5.01  tff(c_10384, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_78, c_10360])).
% 11.76/5.01  tff(c_10396, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10384])).
% 11.76/5.01  tff(c_3279, plain, (![A_233, C_234, B_235]: (r1_tarski(k2_xboole_0(A_233, C_234), B_235) | ~r1_tarski(C_234, B_235) | ~r1_tarski(A_233, B_235))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.76/5.01  tff(c_28568, plain, (![A_654, B_655]: (r1_tarski(k3_relat_1(A_654), B_655) | ~r1_tarski(k2_relat_1(A_654), B_655) | ~r1_tarski(k1_relat_1(A_654), B_655) | ~v1_relat_1(A_654))), inference(superposition, [status(thm), theory('equality')], [c_78, c_3279])).
% 11.76/5.01  tff(c_84, plain, (~r1_tarski(k3_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.76/5.01  tff(c_28655, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_28568, c_84])).
% 11.76/5.01  tff(c_28691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_9754, c_10396, c_28655])).
% 11.76/5.01  tff(c_28693, plain, (![B_656]: (~r1_xboole_0(k1_xboole_0, B_656))), inference(splitRight, [status(thm)], [c_548])).
% 11.76/5.01  tff(c_28697, plain, (![B_35]: (k4_xboole_0(k1_xboole_0, B_35)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_28693])).
% 11.76/5.01  tff(c_28701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_28697])).
% 11.76/5.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.76/5.01  
% 11.76/5.01  Inference rules
% 11.76/5.01  ----------------------
% 11.76/5.01  #Ref     : 1
% 11.76/5.01  #Sup     : 7139
% 11.76/5.01  #Fact    : 0
% 11.76/5.01  #Define  : 0
% 11.76/5.01  #Split   : 14
% 11.76/5.01  #Chain   : 0
% 11.76/5.01  #Close   : 0
% 11.76/5.01  
% 11.76/5.01  Ordering : KBO
% 11.76/5.01  
% 11.76/5.01  Simplification rules
% 11.76/5.01  ----------------------
% 11.76/5.01  #Subsume      : 1707
% 11.76/5.01  #Demod        : 3864
% 11.76/5.01  #Tautology    : 3006
% 11.76/5.01  #SimpNegUnit  : 122
% 11.76/5.01  #BackRed      : 5
% 11.76/5.01  
% 11.76/5.01  #Partial instantiations: 0
% 11.76/5.01  #Strategies tried      : 1
% 11.76/5.01  
% 11.76/5.01  Timing (in seconds)
% 11.76/5.01  ----------------------
% 11.76/5.01  Preprocessing        : 0.36
% 11.76/5.01  Parsing              : 0.19
% 11.76/5.01  CNF conversion       : 0.03
% 11.76/5.01  Main loop            : 3.87
% 11.76/5.01  Inferencing          : 0.71
% 11.76/5.01  Reduction            : 1.89
% 11.76/5.01  Demodulation         : 1.52
% 11.76/5.01  BG Simplification    : 0.08
% 11.76/5.01  Subsumption          : 0.98
% 11.76/5.01  Abstraction          : 0.11
% 11.76/5.01  MUC search           : 0.00
% 11.76/5.01  Cooper               : 0.00
% 11.76/5.01  Total                : 4.28
% 11.76/5.01  Index Insertion      : 0.00
% 11.76/5.01  Index Deletion       : 0.00
% 11.76/5.01  Index Matching       : 0.00
% 11.76/5.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
