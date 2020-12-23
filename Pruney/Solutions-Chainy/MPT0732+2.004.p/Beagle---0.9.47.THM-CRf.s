%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 11.16s
% Output     : CNFRefutation 11.16s
% Verified   : 
% Statistics : Number of formulae       :  112 (1241 expanded)
%              Number of leaves         :   38 ( 430 expanded)
%              Depth                    :   21
%              Number of atoms          :  144 (1646 expanded)
%              Number of equality atoms :   54 ( 891 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_ordinal1 > k5_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_ordinal1(C)
       => ( ( r2_hidden(A,B)
            & r2_hidden(B,C) )
         => r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_104,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_108,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    ! [B_36,C_37] :
      ( k4_xboole_0(k2_tarski(B_36,B_36),C_37) = k1_tarski(B_36)
      | r2_hidden(B_36,C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [A_47,F_52,I_57,E_51,D_50,C_49,B_48] : r2_hidden(I_57,k5_enumset1(A_47,B_48,C_49,D_50,E_51,F_52,I_57)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k3_tarski(B_39))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_182,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_1459,plain,(
    ! [A_203,B_204] : k2_xboole_0(k4_xboole_0(A_203,B_204),k4_xboole_0(B_204,A_203)) = k5_xboole_0(A_203,B_204) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1604,plain,(
    ! [A_214] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_214,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1459])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1617,plain,(
    ! [A_214] :
      ( k5_xboole_0(k1_xboole_0,A_214) = A_214
      | ~ r1_tarski(k1_xboole_0,A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_22])).

tff(c_1665,plain,(
    ! [A_214] : k5_xboole_0(k1_xboole_0,A_214) = A_214 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1617])).

tff(c_227,plain,(
    ! [A_86,B_87] : k2_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = A_86 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_12] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_12),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_227])).

tff(c_254,plain,(
    ! [A_88] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_88),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_227])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    ! [A_88] : k4_xboole_0(k3_xboole_0(k1_xboole_0,A_88),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_20])).

tff(c_274,plain,(
    ! [A_88] : k4_xboole_0(k3_xboole_0(k1_xboole_0,A_88),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_259])).

tff(c_14,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_445,plain,(
    ! [A_99,B_100] : k2_xboole_0(A_99,k4_xboole_0(A_99,k2_xboole_0(A_99,B_100))) = A_99 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_227])).

tff(c_472,plain,(
    ! [A_12] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_12),k4_xboole_0(k3_xboole_0(k1_xboole_0,A_12),k1_xboole_0)) = k3_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_445])).

tff(c_493,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_274,c_472])).

tff(c_1957,plain,(
    ! [A_229,B_230,C_231] :
      ( r1_xboole_0(A_229,k3_xboole_0(B_230,C_231))
      | ~ r1_tarski(A_229,k5_xboole_0(B_230,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1976,plain,(
    ! [A_229,A_12] :
      ( r1_xboole_0(A_229,k1_xboole_0)
      | ~ r1_tarski(A_229,k5_xboole_0(k1_xboole_0,A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1957])).

tff(c_1989,plain,(
    ! [A_232,A_233] :
      ( r1_xboole_0(A_232,k1_xboole_0)
      | ~ r1_tarski(A_232,A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1976])).

tff(c_2053,plain,(
    ! [A_235,B_236] :
      ( r1_xboole_0(A_235,k1_xboole_0)
      | ~ r2_hidden(A_235,B_236) ) ),
    inference(resolution,[status(thm)],[c_42,c_1989])).

tff(c_2090,plain,(
    ! [I_57] : r1_xboole_0(I_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_2053])).

tff(c_110,plain,(
    v1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_106,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_320,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,A_92)
      | ~ r2_hidden(B_91,A_92)
      | ~ v1_ordinal1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_326,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_320])).

tff(c_333,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_326])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_347,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_6])).

tff(c_945,plain,(
    ! [B_145,A_146,C_147] :
      ( r1_xboole_0(B_145,k4_xboole_0(A_146,C_147))
      | ~ r1_xboole_0(A_146,k4_xboole_0(B_145,C_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_951,plain,(
    ! [A_146] :
      ( r1_xboole_0('#skF_5',k4_xboole_0(A_146,'#skF_6'))
      | ~ r1_xboole_0(A_146,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_945])).

tff(c_2147,plain,(
    ! [A_243] : r1_xboole_0('#skF_5',k4_xboole_0(A_243,'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_951])).

tff(c_2153,plain,(
    ! [B_36] :
      ( r1_xboole_0('#skF_5',k1_tarski(B_36))
      | r2_hidden(B_36,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2147])).

tff(c_1511,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_12,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1459])).

tff(c_1711,plain,(
    ! [A_223] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_223,k1_xboole_0)) = A_223 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1511])).

tff(c_1731,plain,(
    ! [A_223] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_223,k1_xboole_0)) = k4_xboole_0(A_223,k4_xboole_0(A_223,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_20])).

tff(c_1771,plain,(
    ! [A_223] : k4_xboole_0(A_223,k4_xboole_0(A_223,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1731])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1678,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_12,k1_xboole_0)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1511])).

tff(c_1757,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_13,k1_xboole_0)) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1711])).

tff(c_1781,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1757])).

tff(c_1514,plain,(
    ! [A_12] : k2_xboole_0(k4_xboole_0(A_12,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1459])).

tff(c_1854,plain,(
    ! [A_227] : k5_xboole_0(A_227,k1_xboole_0) = k4_xboole_0(A_227,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1514])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k2_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1868,plain,(
    ! [A_5,A_227] :
      ( r1_tarski(A_5,k2_xboole_0(A_227,k1_xboole_0))
      | ~ r1_tarski(A_5,k4_xboole_0(A_227,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_12])).

tff(c_2631,plain,(
    ! [A_298,A_299] :
      ( r1_tarski(A_298,A_299)
      | ~ r1_tarski(A_298,k4_xboole_0(A_299,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1868])).

tff(c_3387,plain,(
    ! [A_344,A_345] :
      ( r1_tarski(A_344,A_345)
      | k4_xboole_0(A_344,k4_xboole_0(A_345,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2631])).

tff(c_3429,plain,(
    ! [A_346] : r1_tarski(A_346,A_346) ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_3387])).

tff(c_1883,plain,(
    ! [A_5,A_227] :
      ( r1_tarski(A_5,A_227)
      | ~ r1_tarski(A_5,k4_xboole_0(A_227,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1868])).

tff(c_3485,plain,(
    ! [A_227] : r1_tarski(k4_xboole_0(A_227,k1_xboole_0),A_227) ),
    inference(resolution,[status(thm)],[c_3429,c_1883])).

tff(c_1888,plain,(
    ! [A_228] : k4_xboole_0(A_228,k4_xboole_0(A_228,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1731])).

tff(c_1918,plain,(
    ! [A_228] :
      ( k2_xboole_0(k4_xboole_0(A_228,k1_xboole_0),k1_xboole_0) = A_228
      | ~ r1_tarski(k4_xboole_0(A_228,k1_xboole_0),A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1888,c_22])).

tff(c_1951,plain,(
    ! [A_228] :
      ( k4_xboole_0(A_228,k1_xboole_0) = A_228
      | ~ r1_tarski(k4_xboole_0(A_228,k1_xboole_0),A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1918])).

tff(c_3790,plain,(
    ! [A_228] : k4_xboole_0(A_228,k1_xboole_0) = A_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3485,c_1951])).

tff(c_3885,plain,(
    ! [A_359] : k4_xboole_0(A_359,k1_xboole_0) = A_359 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3485,c_1951])).

tff(c_26,plain,(
    ! [B_20,A_19,C_21] :
      ( r1_xboole_0(B_20,k4_xboole_0(A_19,C_21))
      | ~ r1_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3912,plain,(
    ! [A_359,A_19] :
      ( r1_xboole_0(A_359,k4_xboole_0(A_19,k1_xboole_0))
      | ~ r1_xboole_0(A_19,A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3885,c_26])).

tff(c_4465,plain,(
    ! [A_400,A_401] :
      ( r1_xboole_0(A_400,A_401)
      | ~ r1_xboole_0(A_401,A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3790,c_3912])).

tff(c_4491,plain,(
    ! [B_36] :
      ( r1_xboole_0(k1_tarski(B_36),'#skF_5')
      | r2_hidden(B_36,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2153,c_4465])).

tff(c_2104,plain,(
    ! [I_237] : r1_xboole_0(I_237,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_2053])).

tff(c_48,plain,(
    ! [A_44,C_46,B_45] :
      ( ~ r2_hidden(A_44,C_46)
      | ~ r1_xboole_0(k2_tarski(A_44,B_45),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2109,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2104,c_48])).

tff(c_3955,plain,(
    ! [B_36] :
      ( k2_tarski(B_36,B_36) = k1_tarski(B_36)
      | r2_hidden(B_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3885])).

tff(c_4192,plain,(
    ! [B_372] : k2_tarski(B_372,B_372) = k1_tarski(B_372) ),
    inference(negUnitSimplification,[status(thm)],[c_2109,c_3955])).

tff(c_13945,plain,(
    ! [B_22457,C_22458] :
      ( ~ r2_hidden(B_22457,C_22458)
      | ~ r1_xboole_0(k1_tarski(B_22457),C_22458) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4192,c_48])).

tff(c_13994,plain,(
    ! [B_22623] :
      ( ~ r2_hidden(B_22623,'#skF_5')
      | r2_hidden(B_22623,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4491,c_13945])).

tff(c_14001,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_13994])).

tff(c_14008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n008.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 20:57:00 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.16/4.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/4.58  
% 11.16/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/4.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_ordinal1 > k5_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 11.16/4.58  
% 11.16/4.58  %Foreground sorts:
% 11.16/4.58  
% 11.16/4.58  
% 11.16/4.58  %Background operators:
% 11.16/4.58  
% 11.16/4.58  
% 11.16/4.58  %Foreground operators:
% 11.16/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.16/4.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.16/4.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.16/4.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.16/4.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.16/4.58  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 11.16/4.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.16/4.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.16/4.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.16/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.16/4.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.16/4.58  tff('#skF_5', type, '#skF_5': $i).
% 11.16/4.58  tff('#skF_6', type, '#skF_6': $i).
% 11.16/4.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.16/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.16/4.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.16/4.58  tff('#skF_4', type, '#skF_4': $i).
% 11.16/4.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.16/4.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.16/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.16/4.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.16/4.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.16/4.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.16/4.58  
% 11.16/4.60  tff(f_126, negated_conjecture, ~(![A, B, C]: (v1_ordinal1(C) => ((r2_hidden(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_ordinal1)).
% 11.16/4.60  tff(f_70, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 11.16/4.60  tff(f_110, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 11.16/4.60  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 11.16/4.60  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.16/4.60  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.16/4.60  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 11.16/4.60  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 11.16/4.60  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.16/4.60  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.16/4.60  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 11.16/4.60  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 11.16/4.60  tff(f_117, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 11.16/4.60  tff(f_55, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.16/4.60  tff(f_83, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 11.16/4.60  tff(c_104, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.16/4.60  tff(c_108, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.16/4.60  tff(c_38, plain, (![B_36, C_37]: (k4_xboole_0(k2_tarski(B_36, B_36), C_37)=k1_tarski(B_36) | r2_hidden(B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.16/4.60  tff(c_52, plain, (![A_47, F_52, I_57, E_51, D_50, C_49, B_48]: (r2_hidden(I_57, k5_enumset1(A_47, B_48, C_49, D_50, E_51, F_52, I_57)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.16/4.60  tff(c_42, plain, (![A_38, B_39]: (r1_tarski(A_38, k3_tarski(B_39)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.16/4.60  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.16/4.60  tff(c_182, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.60  tff(c_190, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_182])).
% 11.16/4.60  tff(c_1459, plain, (![A_203, B_204]: (k2_xboole_0(k4_xboole_0(A_203, B_204), k4_xboole_0(B_204, A_203))=k5_xboole_0(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.16/4.60  tff(c_1604, plain, (![A_214]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_214, k1_xboole_0))=k5_xboole_0(k1_xboole_0, A_214))), inference(superposition, [status(thm), theory('equality')], [c_190, c_1459])).
% 11.16/4.60  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.16/4.60  tff(c_1617, plain, (![A_214]: (k5_xboole_0(k1_xboole_0, A_214)=A_214 | ~r1_tarski(k1_xboole_0, A_214))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_22])).
% 11.16/4.60  tff(c_1665, plain, (![A_214]: (k5_xboole_0(k1_xboole_0, A_214)=A_214)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1617])).
% 11.16/4.60  tff(c_227, plain, (![A_86, B_87]: (k2_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=A_86)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.16/4.60  tff(c_245, plain, (![A_12]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_12), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_227])).
% 11.16/4.60  tff(c_254, plain, (![A_88]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_88), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_227])).
% 11.16/4.60  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.16/4.60  tff(c_259, plain, (![A_88]: (k4_xboole_0(k3_xboole_0(k1_xboole_0, A_88), k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_254, c_20])).
% 11.16/4.60  tff(c_274, plain, (![A_88]: (k4_xboole_0(k3_xboole_0(k1_xboole_0, A_88), k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_259])).
% 11.16/4.60  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.16/4.60  tff(c_445, plain, (![A_99, B_100]: (k2_xboole_0(A_99, k4_xboole_0(A_99, k2_xboole_0(A_99, B_100)))=A_99)), inference(superposition, [status(thm), theory('equality')], [c_14, c_227])).
% 11.16/4.60  tff(c_472, plain, (![A_12]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_12), k4_xboole_0(k3_xboole_0(k1_xboole_0, A_12), k1_xboole_0))=k3_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_245, c_445])).
% 11.16/4.60  tff(c_493, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_274, c_472])).
% 11.16/4.60  tff(c_1957, plain, (![A_229, B_230, C_231]: (r1_xboole_0(A_229, k3_xboole_0(B_230, C_231)) | ~r1_tarski(A_229, k5_xboole_0(B_230, C_231)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.16/4.60  tff(c_1976, plain, (![A_229, A_12]: (r1_xboole_0(A_229, k1_xboole_0) | ~r1_tarski(A_229, k5_xboole_0(k1_xboole_0, A_12)))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1957])).
% 11.16/4.60  tff(c_1989, plain, (![A_232, A_233]: (r1_xboole_0(A_232, k1_xboole_0) | ~r1_tarski(A_232, A_233))), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1976])).
% 11.16/4.60  tff(c_2053, plain, (![A_235, B_236]: (r1_xboole_0(A_235, k1_xboole_0) | ~r2_hidden(A_235, B_236))), inference(resolution, [status(thm)], [c_42, c_1989])).
% 11.16/4.60  tff(c_2090, plain, (![I_57]: (r1_xboole_0(I_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_2053])).
% 11.16/4.60  tff(c_110, plain, (v1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.16/4.60  tff(c_106, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.16/4.60  tff(c_320, plain, (![B_91, A_92]: (r1_tarski(B_91, A_92) | ~r2_hidden(B_91, A_92) | ~v1_ordinal1(A_92))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.16/4.60  tff(c_326, plain, (r1_tarski('#skF_5', '#skF_6') | ~v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_106, c_320])).
% 11.16/4.60  tff(c_333, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_326])).
% 11.16/4.60  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.60  tff(c_347, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_333, c_6])).
% 11.16/4.60  tff(c_945, plain, (![B_145, A_146, C_147]: (r1_xboole_0(B_145, k4_xboole_0(A_146, C_147)) | ~r1_xboole_0(A_146, k4_xboole_0(B_145, C_147)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.16/4.60  tff(c_951, plain, (![A_146]: (r1_xboole_0('#skF_5', k4_xboole_0(A_146, '#skF_6')) | ~r1_xboole_0(A_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_347, c_945])).
% 11.16/4.60  tff(c_2147, plain, (![A_243]: (r1_xboole_0('#skF_5', k4_xboole_0(A_243, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2090, c_951])).
% 11.16/4.60  tff(c_2153, plain, (![B_36]: (r1_xboole_0('#skF_5', k1_tarski(B_36)) | r2_hidden(B_36, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2147])).
% 11.16/4.60  tff(c_1511, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_12, k1_xboole_0))=k5_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_190, c_1459])).
% 11.16/4.60  tff(c_1711, plain, (![A_223]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_223, k1_xboole_0))=A_223)), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1511])).
% 11.16/4.60  tff(c_1731, plain, (![A_223]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_223, k1_xboole_0))=k4_xboole_0(A_223, k4_xboole_0(A_223, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1711, c_20])).
% 11.16/4.60  tff(c_1771, plain, (![A_223]: (k4_xboole_0(A_223, k4_xboole_0(A_223, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_1731])).
% 11.16/4.60  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.60  tff(c_1678, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_12, k1_xboole_0))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1511])).
% 11.16/4.60  tff(c_1757, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_13, k1_xboole_0))=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1711])).
% 11.16/4.60  tff(c_1781, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1757])).
% 11.16/4.60  tff(c_1514, plain, (![A_12]: (k2_xboole_0(k4_xboole_0(A_12, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_1459])).
% 11.16/4.60  tff(c_1854, plain, (![A_227]: (k5_xboole_0(A_227, k1_xboole_0)=k4_xboole_0(A_227, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1514])).
% 11.16/4.60  tff(c_12, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k2_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.16/4.60  tff(c_1868, plain, (![A_5, A_227]: (r1_tarski(A_5, k2_xboole_0(A_227, k1_xboole_0)) | ~r1_tarski(A_5, k4_xboole_0(A_227, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_12])).
% 11.16/4.60  tff(c_2631, plain, (![A_298, A_299]: (r1_tarski(A_298, A_299) | ~r1_tarski(A_298, k4_xboole_0(A_299, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1868])).
% 11.16/4.60  tff(c_3387, plain, (![A_344, A_345]: (r1_tarski(A_344, A_345) | k4_xboole_0(A_344, k4_xboole_0(A_345, k1_xboole_0))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2631])).
% 11.16/4.60  tff(c_3429, plain, (![A_346]: (r1_tarski(A_346, A_346))), inference(superposition, [status(thm), theory('equality')], [c_1771, c_3387])).
% 11.16/4.60  tff(c_1883, plain, (![A_5, A_227]: (r1_tarski(A_5, A_227) | ~r1_tarski(A_5, k4_xboole_0(A_227, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1868])).
% 11.16/4.60  tff(c_3485, plain, (![A_227]: (r1_tarski(k4_xboole_0(A_227, k1_xboole_0), A_227))), inference(resolution, [status(thm)], [c_3429, c_1883])).
% 11.16/4.60  tff(c_1888, plain, (![A_228]: (k4_xboole_0(A_228, k4_xboole_0(A_228, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_1731])).
% 11.16/4.60  tff(c_1918, plain, (![A_228]: (k2_xboole_0(k4_xboole_0(A_228, k1_xboole_0), k1_xboole_0)=A_228 | ~r1_tarski(k4_xboole_0(A_228, k1_xboole_0), A_228))), inference(superposition, [status(thm), theory('equality')], [c_1888, c_22])).
% 11.16/4.60  tff(c_1951, plain, (![A_228]: (k4_xboole_0(A_228, k1_xboole_0)=A_228 | ~r1_tarski(k4_xboole_0(A_228, k1_xboole_0), A_228))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1918])).
% 11.16/4.60  tff(c_3790, plain, (![A_228]: (k4_xboole_0(A_228, k1_xboole_0)=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_3485, c_1951])).
% 11.16/4.60  tff(c_3885, plain, (![A_359]: (k4_xboole_0(A_359, k1_xboole_0)=A_359)), inference(demodulation, [status(thm), theory('equality')], [c_3485, c_1951])).
% 11.16/4.60  tff(c_26, plain, (![B_20, A_19, C_21]: (r1_xboole_0(B_20, k4_xboole_0(A_19, C_21)) | ~r1_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.16/4.60  tff(c_3912, plain, (![A_359, A_19]: (r1_xboole_0(A_359, k4_xboole_0(A_19, k1_xboole_0)) | ~r1_xboole_0(A_19, A_359))), inference(superposition, [status(thm), theory('equality')], [c_3885, c_26])).
% 11.16/4.60  tff(c_4465, plain, (![A_400, A_401]: (r1_xboole_0(A_400, A_401) | ~r1_xboole_0(A_401, A_400))), inference(demodulation, [status(thm), theory('equality')], [c_3790, c_3912])).
% 11.16/4.60  tff(c_4491, plain, (![B_36]: (r1_xboole_0(k1_tarski(B_36), '#skF_5') | r2_hidden(B_36, '#skF_6'))), inference(resolution, [status(thm)], [c_2153, c_4465])).
% 11.16/4.60  tff(c_2104, plain, (![I_237]: (r1_xboole_0(I_237, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_2053])).
% 11.16/4.60  tff(c_48, plain, (![A_44, C_46, B_45]: (~r2_hidden(A_44, C_46) | ~r1_xboole_0(k2_tarski(A_44, B_45), C_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.16/4.60  tff(c_2109, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_2104, c_48])).
% 11.16/4.60  tff(c_3955, plain, (![B_36]: (k2_tarski(B_36, B_36)=k1_tarski(B_36) | r2_hidden(B_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3885])).
% 11.16/4.60  tff(c_4192, plain, (![B_372]: (k2_tarski(B_372, B_372)=k1_tarski(B_372))), inference(negUnitSimplification, [status(thm)], [c_2109, c_3955])).
% 11.16/4.60  tff(c_13945, plain, (![B_22457, C_22458]: (~r2_hidden(B_22457, C_22458) | ~r1_xboole_0(k1_tarski(B_22457), C_22458))), inference(superposition, [status(thm), theory('equality')], [c_4192, c_48])).
% 11.16/4.60  tff(c_13994, plain, (![B_22623]: (~r2_hidden(B_22623, '#skF_5') | r2_hidden(B_22623, '#skF_6'))), inference(resolution, [status(thm)], [c_4491, c_13945])).
% 11.16/4.60  tff(c_14001, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_108, c_13994])).
% 11.16/4.60  tff(c_14008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_14001])).
% 11.16/4.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/4.60  
% 11.16/4.60  Inference rules
% 11.16/4.60  ----------------------
% 11.16/4.60  #Ref     : 0
% 11.16/4.60  #Sup     : 2664
% 11.16/4.60  #Fact    : 168
% 11.16/4.60  #Define  : 0
% 11.16/4.60  #Split   : 3
% 11.16/4.60  #Chain   : 0
% 11.16/4.60  #Close   : 0
% 11.16/4.60  
% 11.16/4.60  Ordering : KBO
% 11.16/4.60  
% 11.16/4.60  Simplification rules
% 11.16/4.60  ----------------------
% 11.16/4.60  #Subsume      : 995
% 11.16/4.60  #Demod        : 664
% 11.16/4.60  #Tautology    : 790
% 11.16/4.60  #SimpNegUnit  : 64
% 11.16/4.60  #BackRed      : 42
% 11.16/4.60  
% 11.16/4.60  #Partial instantiations: 8672
% 11.16/4.60  #Strategies tried      : 1
% 11.16/4.60  
% 11.16/4.60  Timing (in seconds)
% 11.16/4.60  ----------------------
% 11.16/4.60  Preprocessing        : 0.33
% 11.16/4.60  Parsing              : 0.16
% 11.16/4.60  CNF conversion       : 0.03
% 11.16/4.60  Main loop            : 3.56
% 11.16/4.60  Inferencing          : 1.66
% 11.16/4.60  Reduction            : 0.78
% 11.16/4.60  Demodulation         : 0.62
% 11.16/4.60  BG Simplification    : 0.15
% 11.16/4.60  Subsumption          : 0.86
% 11.16/4.60  Abstraction          : 0.33
% 11.16/4.60  MUC search           : 0.00
% 11.16/4.60  Cooper               : 0.00
% 11.16/4.60  Total                : 3.93
% 11.16/4.60  Index Insertion      : 0.00
% 11.16/4.60  Index Deletion       : 0.00
% 11.16/4.60  Index Matching       : 0.00
% 11.16/4.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
