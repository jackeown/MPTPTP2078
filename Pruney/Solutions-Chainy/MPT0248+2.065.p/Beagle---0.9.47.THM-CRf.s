%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 586 expanded)
%              Number of leaves         :   34 ( 210 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 755 expanded)
%              Number of equality atoms :   95 ( 667 expanded)
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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_52,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_91,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_112,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_112])).

tff(c_630,plain,(
    ! [B_104,A_105] :
      ( k1_tarski(B_104) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_644,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_115,c_630])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_91,c_644])).

tff(c_661,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_662,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_663,plain,(
    ! [A_16] : r1_tarski('#skF_2',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_104])).

tff(c_947,plain,(
    ! [A_130,B_131] :
      ( k2_xboole_0(A_130,B_131) = B_131
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_966,plain,(
    ! [A_16] : k2_xboole_0('#skF_2',A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_663,c_947])).

tff(c_968,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_56])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_968])).

tff(c_971,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_972,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1016,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_972,c_54])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1399,plain,(
    ! [A_165,B_166] : k5_xboole_0(A_165,k3_xboole_0(A_165,B_166)) = k4_xboole_0(A_165,B_166) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1417,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1399])).

tff(c_1421,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1417])).

tff(c_984,plain,(
    ! [A_132,B_133] : r1_tarski(k3_xboole_0(A_132,B_133),A_132) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_987,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_984])).

tff(c_1233,plain,(
    ! [A_156,B_157] :
      ( k2_xboole_0(A_156,B_157) = B_157
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1260,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_987,c_1233])).

tff(c_1017,plain,(
    ! [B_139,A_140] : k3_xboole_0(B_139,A_140) = k3_xboole_0(A_140,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1039,plain,(
    ! [A_140] : k3_xboole_0(k1_xboole_0,A_140) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_18])).

tff(c_2187,plain,(
    ! [A_196,B_197] : k4_xboole_0(k2_xboole_0(A_196,B_197),k3_xboole_0(A_196,B_197)) = k5_xboole_0(A_196,B_197) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2232,plain,(
    ! [A_140] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_140),k1_xboole_0) = k5_xboole_0(k1_xboole_0,A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_2187])).

tff(c_2256,plain,(
    ! [A_140] : k5_xboole_0(k1_xboole_0,A_140) = A_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1260,c_2232])).

tff(c_2244,plain,(
    ! [A_16] : k4_xboole_0(k2_xboole_0(A_16,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2187])).

tff(c_2260,plain,(
    ! [A_198] : k2_xboole_0(A_198,k1_xboole_0) = A_198 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_20,c_2244])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1138,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k1_xboole_0
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1164,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1138])).

tff(c_2284,plain,(
    ! [A_198] : k4_xboole_0(A_198,A_198) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2260,c_1164])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1720,plain,(
    ! [A_181,B_182,C_183] : k5_xboole_0(k5_xboole_0(A_181,B_182),C_183) = k5_xboole_0(A_181,k5_xboole_0(B_182,C_183)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1765,plain,(
    ! [A_181,B_182] : k5_xboole_0(A_181,k5_xboole_0(B_182,k5_xboole_0(A_181,B_182))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1720])).

tff(c_1761,plain,(
    ! [A_23,C_183] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_183)) = k5_xboole_0(k1_xboole_0,C_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1720])).

tff(c_2921,plain,(
    ! [A_219,C_220] : k5_xboole_0(A_219,k5_xboole_0(A_219,C_220)) = C_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_1761])).

tff(c_2965,plain,(
    ! [B_182,A_181] : k5_xboole_0(B_182,k5_xboole_0(A_181,B_182)) = k5_xboole_0(A_181,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_2921])).

tff(c_3008,plain,(
    ! [B_221,A_222] : k5_xboole_0(B_221,k5_xboole_0(A_222,B_221)) = A_222 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2965])).

tff(c_2920,plain,(
    ! [A_23,C_183] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_183)) = C_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_1761])).

tff(c_3017,plain,(
    ! [B_221,A_222] : k5_xboole_0(B_221,A_222) = k5_xboole_0(A_222,B_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_3008,c_2920])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1032,plain,(
    ! [B_139,A_140] : r1_tarski(k3_xboole_0(B_139,A_140),A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_16])).

tff(c_1585,plain,(
    ! [B_176,A_177] :
      ( k1_tarski(B_176) = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,k1_tarski(B_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1607,plain,(
    ! [A_177] :
      ( k1_tarski('#skF_1') = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_1585])).

tff(c_1689,plain,(
    ! [A_180] :
      ( A_180 = '#skF_2'
      | k1_xboole_0 = A_180
      | ~ r1_tarski(A_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_1607])).

tff(c_1710,plain,(
    ! [B_139] :
      ( k3_xboole_0(B_139,'#skF_2') = '#skF_2'
      | k3_xboole_0(B_139,'#skF_2') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1032,c_1689])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_979,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_56])).

tff(c_2241,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_2187])).

tff(c_2257,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2241])).

tff(c_2419,plain,
    ( k5_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_2',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_2257])).

tff(c_2422,plain,
    ( k5_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_2419])).

tff(c_4294,plain,
    ( k5_xboole_0('#skF_3','#skF_2') = '#skF_2'
    | k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3017,c_2422])).

tff(c_4295,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4294])).

tff(c_3165,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3017,c_2257])).

tff(c_4296,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4295,c_3165])).

tff(c_4297,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_4296])).

tff(c_3001,plain,(
    ! [B_182,A_181] : k5_xboole_0(B_182,k5_xboole_0(A_181,B_182)) = A_181 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2965])).

tff(c_3011,plain,(
    ! [A_222,B_221] : k5_xboole_0(k5_xboole_0(A_222,B_221),A_222) = B_221 ),
    inference(superposition,[status(thm),theory(equality)],[c_3008,c_3001])).

tff(c_4513,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4297,c_3011])).

tff(c_4525,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_4513])).

tff(c_4527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1016,c_4525])).

tff(c_4528,plain,(
    k5_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4294])).

tff(c_3041,plain,(
    ! [A_23,C_183] : k5_xboole_0(k5_xboole_0(A_23,C_183),C_183) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_2920,c_3008])).

tff(c_4534,plain,(
    k5_xboole_0('#skF_2','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4528,c_3041])).

tff(c_4574,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4534,c_26])).

tff(c_4583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_971,c_4574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.85  
% 4.36/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.86  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.36/1.86  
% 4.36/1.86  %Foreground sorts:
% 4.36/1.86  
% 4.36/1.86  
% 4.36/1.86  %Background operators:
% 4.36/1.86  
% 4.36/1.86  
% 4.36/1.86  %Foreground operators:
% 4.36/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.36/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.36/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.36/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.36/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.36/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.36/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.36/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.36/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.36/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.36/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.86  
% 4.36/1.88  tff(f_94, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.36/1.88  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.36/1.88  tff(f_73, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.36/1.88  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.36/1.88  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.36/1.88  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.36/1.88  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.36/1.88  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.36/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.36/1.88  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.36/1.88  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.36/1.88  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.36/1.88  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.36/1.88  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.36/1.88  tff(c_107, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 4.36/1.88  tff(c_50, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.36/1.88  tff(c_91, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 4.36/1.88  tff(c_56, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.36/1.88  tff(c_112, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.88  tff(c_115, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_112])).
% 4.36/1.88  tff(c_630, plain, (![B_104, A_105]: (k1_tarski(B_104)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(B_104)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.36/1.88  tff(c_644, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_115, c_630])).
% 4.36/1.88  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_91, c_644])).
% 4.36/1.88  tff(c_661, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 4.36/1.88  tff(c_662, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 4.36/1.88  tff(c_18, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.88  tff(c_101, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.88  tff(c_104, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_101])).
% 4.36/1.88  tff(c_663, plain, (![A_16]: (r1_tarski('#skF_2', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_104])).
% 4.36/1.88  tff(c_947, plain, (![A_130, B_131]: (k2_xboole_0(A_130, B_131)=B_131 | ~r1_tarski(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.88  tff(c_966, plain, (![A_16]: (k2_xboole_0('#skF_2', A_16)=A_16)), inference(resolution, [status(thm)], [c_663, c_947])).
% 4.36/1.88  tff(c_968, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_966, c_56])).
% 4.36/1.88  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_661, c_968])).
% 4.36/1.88  tff(c_971, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 4.36/1.88  tff(c_972, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 4.36/1.88  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.36/1.88  tff(c_1016, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_972, c_972, c_54])).
% 4.36/1.88  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.36/1.88  tff(c_1399, plain, (![A_165, B_166]: (k5_xboole_0(A_165, k3_xboole_0(A_165, B_166))=k4_xboole_0(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.36/1.88  tff(c_1417, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1399])).
% 4.36/1.88  tff(c_1421, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1417])).
% 4.36/1.88  tff(c_984, plain, (![A_132, B_133]: (r1_tarski(k3_xboole_0(A_132, B_133), A_132))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.88  tff(c_987, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_984])).
% 4.36/1.88  tff(c_1233, plain, (![A_156, B_157]: (k2_xboole_0(A_156, B_157)=B_157 | ~r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.88  tff(c_1260, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, A_16)=A_16)), inference(resolution, [status(thm)], [c_987, c_1233])).
% 4.36/1.88  tff(c_1017, plain, (![B_139, A_140]: (k3_xboole_0(B_139, A_140)=k3_xboole_0(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.36/1.88  tff(c_1039, plain, (![A_140]: (k3_xboole_0(k1_xboole_0, A_140)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1017, c_18])).
% 4.36/1.88  tff(c_2187, plain, (![A_196, B_197]: (k4_xboole_0(k2_xboole_0(A_196, B_197), k3_xboole_0(A_196, B_197))=k5_xboole_0(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.88  tff(c_2232, plain, (![A_140]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_140), k1_xboole_0)=k5_xboole_0(k1_xboole_0, A_140))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_2187])).
% 4.36/1.88  tff(c_2256, plain, (![A_140]: (k5_xboole_0(k1_xboole_0, A_140)=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1260, c_2232])).
% 4.36/1.88  tff(c_2244, plain, (![A_16]: (k4_xboole_0(k2_xboole_0(A_16, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2187])).
% 4.36/1.88  tff(c_2260, plain, (![A_198]: (k2_xboole_0(A_198, k1_xboole_0)=A_198)), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_20, c_2244])).
% 4.36/1.88  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.88  tff(c_1138, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k1_xboole_0 | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.88  tff(c_1164, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1138])).
% 4.36/1.88  tff(c_2284, plain, (![A_198]: (k4_xboole_0(A_198, A_198)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2260, c_1164])).
% 4.36/1.88  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.88  tff(c_1720, plain, (![A_181, B_182, C_183]: (k5_xboole_0(k5_xboole_0(A_181, B_182), C_183)=k5_xboole_0(A_181, k5_xboole_0(B_182, C_183)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.36/1.88  tff(c_1765, plain, (![A_181, B_182]: (k5_xboole_0(A_181, k5_xboole_0(B_182, k5_xboole_0(A_181, B_182)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1720])).
% 4.36/1.88  tff(c_1761, plain, (![A_23, C_183]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_183))=k5_xboole_0(k1_xboole_0, C_183))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1720])).
% 4.36/1.88  tff(c_2921, plain, (![A_219, C_220]: (k5_xboole_0(A_219, k5_xboole_0(A_219, C_220))=C_220)), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_1761])).
% 4.36/1.88  tff(c_2965, plain, (![B_182, A_181]: (k5_xboole_0(B_182, k5_xboole_0(A_181, B_182))=k5_xboole_0(A_181, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1765, c_2921])).
% 4.36/1.88  tff(c_3008, plain, (![B_221, A_222]: (k5_xboole_0(B_221, k5_xboole_0(A_222, B_221))=A_222)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2965])).
% 4.36/1.88  tff(c_2920, plain, (![A_23, C_183]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_183))=C_183)), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_1761])).
% 4.36/1.88  tff(c_3017, plain, (![B_221, A_222]: (k5_xboole_0(B_221, A_222)=k5_xboole_0(A_222, B_221))), inference(superposition, [status(thm), theory('equality')], [c_3008, c_2920])).
% 4.36/1.88  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.88  tff(c_1032, plain, (![B_139, A_140]: (r1_tarski(k3_xboole_0(B_139, A_140), A_140))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_16])).
% 4.36/1.88  tff(c_1585, plain, (![B_176, A_177]: (k1_tarski(B_176)=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, k1_tarski(B_176)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.36/1.88  tff(c_1607, plain, (![A_177]: (k1_tarski('#skF_1')=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_972, c_1585])).
% 4.36/1.88  tff(c_1689, plain, (![A_180]: (A_180='#skF_2' | k1_xboole_0=A_180 | ~r1_tarski(A_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_1607])).
% 4.36/1.88  tff(c_1710, plain, (![B_139]: (k3_xboole_0(B_139, '#skF_2')='#skF_2' | k3_xboole_0(B_139, '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1032, c_1689])).
% 4.36/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.36/1.88  tff(c_979, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_972, c_56])).
% 4.36/1.88  tff(c_2241, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_979, c_2187])).
% 4.36/1.88  tff(c_2257, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2241])).
% 4.36/1.88  tff(c_2419, plain, (k5_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_2', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1710, c_2257])).
% 4.36/1.88  tff(c_2422, plain, (k5_xboole_0('#skF_2', '#skF_3')='#skF_2' | k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_2419])).
% 4.36/1.88  tff(c_4294, plain, (k5_xboole_0('#skF_3', '#skF_2')='#skF_2' | k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3017, c_2422])).
% 4.36/1.88  tff(c_4295, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_4294])).
% 4.36/1.88  tff(c_3165, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3017, c_2257])).
% 4.36/1.88  tff(c_4296, plain, (k5_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4295, c_3165])).
% 4.36/1.88  tff(c_4297, plain, (k5_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2284, c_4296])).
% 4.36/1.88  tff(c_3001, plain, (![B_182, A_181]: (k5_xboole_0(B_182, k5_xboole_0(A_181, B_182))=A_181)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2965])).
% 4.36/1.88  tff(c_3011, plain, (![A_222, B_221]: (k5_xboole_0(k5_xboole_0(A_222, B_221), A_222)=B_221)), inference(superposition, [status(thm), theory('equality')], [c_3008, c_3001])).
% 4.36/1.88  tff(c_4513, plain, (k5_xboole_0(k1_xboole_0, '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4297, c_3011])).
% 4.36/1.88  tff(c_4525, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_4513])).
% 4.36/1.88  tff(c_4527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1016, c_4525])).
% 4.36/1.88  tff(c_4528, plain, (k5_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_4294])).
% 4.36/1.88  tff(c_3041, plain, (![A_23, C_183]: (k5_xboole_0(k5_xboole_0(A_23, C_183), C_183)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_2920, c_3008])).
% 4.36/1.88  tff(c_4534, plain, (k5_xboole_0('#skF_2', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4528, c_3041])).
% 4.36/1.88  tff(c_4574, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4534, c_26])).
% 4.36/1.88  tff(c_4583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_971, c_4574])).
% 4.36/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.88  
% 4.36/1.88  Inference rules
% 4.36/1.88  ----------------------
% 4.36/1.88  #Ref     : 0
% 4.36/1.88  #Sup     : 1072
% 4.36/1.88  #Fact    : 4
% 4.36/1.88  #Define  : 0
% 4.36/1.88  #Split   : 4
% 4.36/1.88  #Chain   : 0
% 4.36/1.88  #Close   : 0
% 4.36/1.88  
% 4.36/1.88  Ordering : KBO
% 4.36/1.88  
% 4.36/1.88  Simplification rules
% 4.36/1.88  ----------------------
% 4.36/1.88  #Subsume      : 42
% 4.36/1.88  #Demod        : 668
% 4.36/1.88  #Tautology    : 768
% 4.36/1.88  #SimpNegUnit  : 46
% 4.36/1.88  #BackRed      : 18
% 4.36/1.88  
% 4.36/1.88  #Partial instantiations: 0
% 4.36/1.88  #Strategies tried      : 1
% 4.36/1.88  
% 4.36/1.88  Timing (in seconds)
% 4.36/1.88  ----------------------
% 4.36/1.88  Preprocessing        : 0.32
% 4.36/1.88  Parsing              : 0.17
% 4.36/1.88  CNF conversion       : 0.02
% 4.36/1.88  Main loop            : 0.78
% 4.36/1.88  Inferencing          : 0.25
% 4.36/1.88  Reduction            : 0.32
% 4.36/1.88  Demodulation         : 0.25
% 4.36/1.88  BG Simplification    : 0.03
% 4.36/1.88  Subsumption          : 0.11
% 4.36/1.88  Abstraction          : 0.04
% 4.36/1.88  MUC search           : 0.00
% 4.36/1.88  Cooper               : 0.00
% 4.36/1.88  Total                : 1.15
% 4.36/1.88  Index Insertion      : 0.00
% 4.36/1.88  Index Deletion       : 0.00
% 4.36/1.88  Index Matching       : 0.00
% 4.36/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
