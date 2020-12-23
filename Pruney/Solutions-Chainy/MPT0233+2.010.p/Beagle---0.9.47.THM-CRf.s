%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 8.82s
% Output     : CNFRefutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 141 expanded)
%              Number of leaves         :   47 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 ( 159 expanded)
%              Number of equality atoms :   71 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_92,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_74,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_72,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_70,plain,(
    ! [A_68,B_69] : k3_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) = k1_tarski(A_68) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_200,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_214,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_200])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_317,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,B_111)
      | ~ r1_tarski(A_110,k3_xboole_0(B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_382,plain,(
    ! [B_119,C_120,B_121] : r1_tarski(k3_xboole_0(k3_xboole_0(B_119,C_120),B_121),B_119) ),
    inference(resolution,[status(thm)],[c_16,c_317])).

tff(c_1209,plain,(
    ! [B_162,A_163,B_164] : r1_tarski(k3_xboole_0(k3_xboole_0(B_162,A_163),B_164),A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_382])).

tff(c_1304,plain,(
    ! [B_170,B_171,A_172] : r1_tarski(k3_xboole_0(B_170,k3_xboole_0(B_171,A_172)),A_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1209])).

tff(c_1568,plain,(
    ! [B_181] : r1_tarski(k3_xboole_0(B_181,k2_tarski('#skF_5','#skF_6')),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_1304])).

tff(c_1582,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1568])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1717,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_1582,c_20])).

tff(c_24,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_349,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,k3_xboole_0(A_113,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_423,plain,(
    ! [A_122,B_123] :
      ( ~ r1_xboole_0(A_122,B_123)
      | k3_xboole_0(A_122,B_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_349])).

tff(c_427,plain,(
    ! [A_26] : k3_xboole_0(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_423])).

tff(c_480,plain,(
    ! [A_125,B_126] : k5_xboole_0(A_125,k3_xboole_0(A_125,B_126)) = k4_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_489,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = k4_xboole_0(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_480])).

tff(c_587,plain,(
    ! [A_129] : k4_xboole_0(A_129,k1_xboole_0) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_489])).

tff(c_22,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_593,plain,(
    ! [A_129] : k4_xboole_0(A_129,A_129) = k3_xboole_0(A_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_22])).

tff(c_601,plain,(
    ! [A_129] : k4_xboole_0(A_129,A_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_593])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_504,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_480])).

tff(c_819,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_504])).

tff(c_1391,plain,(
    ! [A_177,B_178] : k3_xboole_0(k3_xboole_0(A_177,B_178),A_177) = k3_xboole_0(A_177,B_178) ),
    inference(resolution,[status(thm)],[c_16,c_200])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1423,plain,(
    ! [A_177,B_178] : k5_xboole_0(k3_xboole_0(A_177,B_178),k3_xboole_0(A_177,B_178)) = k4_xboole_0(k3_xboole_0(A_177,B_178),A_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_14])).

tff(c_1513,plain,(
    ! [A_179,B_180] : k4_xboole_0(k3_xboole_0(A_179,B_180),A_179) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_1423])).

tff(c_1601,plain,(
    ! [B_182,A_183] : k4_xboole_0(k3_xboole_0(B_182,A_183),A_183) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1513])).

tff(c_28,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1616,plain,(
    ! [A_183,B_182] : k2_xboole_0(A_183,k3_xboole_0(B_182,A_183)) = k5_xboole_0(A_183,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_28])).

tff(c_1654,plain,(
    ! [A_183,B_182] : k2_xboole_0(A_183,k3_xboole_0(B_182,A_183)) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1616])).

tff(c_4707,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_1654])).

tff(c_60,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1777,plain,(
    ! [A_188,B_189,C_190,D_191] : k2_xboole_0(k2_tarski(A_188,B_189),k2_tarski(C_190,D_191)) = k2_enumset1(A_188,B_189,C_190,D_191) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1806,plain,(
    ! [A_40,C_190,D_191] : k2_xboole_0(k1_tarski(A_40),k2_tarski(C_190,D_191)) = k2_enumset1(A_40,A_40,C_190,D_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1777])).

tff(c_1812,plain,(
    ! [A_40,C_190,D_191] : k2_xboole_0(k1_tarski(A_40),k2_tarski(C_190,D_191)) = k1_enumset1(A_40,C_190,D_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1806])).

tff(c_7518,plain,(
    ! [A_349,B_350,A_351] : k2_xboole_0(k2_tarski(A_349,B_350),k1_tarski(A_351)) = k2_enumset1(A_349,B_350,A_351,A_351) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1777])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7535,plain,(
    ! [A_351,A_349,B_350] : k2_xboole_0(k1_tarski(A_351),k2_tarski(A_349,B_350)) = k2_enumset1(A_349,B_350,A_351,A_351) ),
    inference(superposition,[status(thm),theory(equality)],[c_7518,c_2])).

tff(c_7566,plain,(
    ! [A_349,B_350,A_351] : k2_enumset1(A_349,B_350,A_351,A_351) = k1_enumset1(A_351,A_349,B_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_7535])).

tff(c_1809,plain,(
    ! [A_188,B_189,A_40] : k2_xboole_0(k2_tarski(A_188,B_189),k1_tarski(A_40)) = k2_enumset1(A_188,B_189,A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1777])).

tff(c_7715,plain,(
    ! [A_188,B_189,A_40] : k2_xboole_0(k2_tarski(A_188,B_189),k1_tarski(A_40)) = k1_enumset1(A_40,A_188,B_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7566,c_1809])).

tff(c_16588,plain,(
    k1_enumset1('#skF_5','#skF_7','#skF_8') = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4707,c_7715])).

tff(c_36,plain,(
    ! [E_35,B_30,C_31] : r2_hidden(E_35,k1_enumset1(E_35,B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17292,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16588,c_36])).

tff(c_58,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1366,plain,(
    ! [E_173,C_174,B_175,A_176] :
      ( E_173 = C_174
      | E_173 = B_175
      | E_173 = A_176
      | ~ r2_hidden(E_173,k1_enumset1(A_176,B_175,C_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1369,plain,(
    ! [E_173,B_42,A_41] :
      ( E_173 = B_42
      | E_173 = A_41
      | E_173 = A_41
      | ~ r2_hidden(E_173,k2_tarski(A_41,B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1366])).

tff(c_17310,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_17292,c_1369])).

tff(c_17314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_74,c_72,c_17310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.82/3.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.82/3.41  
% 8.82/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.82/3.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 8.82/3.41  
% 8.82/3.41  %Foreground sorts:
% 8.82/3.41  
% 8.82/3.41  
% 8.82/3.41  %Background operators:
% 8.82/3.41  
% 8.82/3.41  
% 8.82/3.41  %Foreground operators:
% 8.82/3.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.82/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.82/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.82/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.82/3.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.82/3.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.82/3.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.82/3.41  tff('#skF_7', type, '#skF_7': $i).
% 8.82/3.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.82/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.82/3.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.82/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.82/3.41  tff('#skF_5', type, '#skF_5': $i).
% 8.82/3.41  tff('#skF_6', type, '#skF_6': $i).
% 8.82/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.82/3.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.82/3.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 8.82/3.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.41  tff('#skF_8', type, '#skF_8': $i).
% 8.82/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.82/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.82/3.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.82/3.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.82/3.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.82/3.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.82/3.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.82/3.41  
% 8.82/3.43  tff(f_116, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 8.82/3.43  tff(f_106, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 8.82/3.43  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.82/3.43  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.82/3.43  tff(f_57, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.82/3.43  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 8.82/3.43  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.82/3.43  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.82/3.43  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.82/3.43  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.82/3.43  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.82/3.43  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.82/3.43  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.82/3.43  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.82/3.43  tff(f_96, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.82/3.43  tff(f_92, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.82/3.43  tff(f_90, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 8.82/3.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.82/3.43  tff(f_88, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 8.82/3.43  tff(f_94, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.82/3.43  tff(c_74, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.82/3.43  tff(c_72, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.82/3.43  tff(c_70, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69))=k1_tarski(A_68))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.82/3.43  tff(c_76, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.82/3.43  tff(c_200, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.82/3.43  tff(c_214, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_76, c_200])).
% 8.82/3.43  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.82/3.43  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.82/3.43  tff(c_317, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, B_111) | ~r1_tarski(A_110, k3_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.82/3.43  tff(c_382, plain, (![B_119, C_120, B_121]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_119, C_120), B_121), B_119))), inference(resolution, [status(thm)], [c_16, c_317])).
% 8.82/3.43  tff(c_1209, plain, (![B_162, A_163, B_164]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_162, A_163), B_164), A_163))), inference(superposition, [status(thm), theory('equality')], [c_4, c_382])).
% 8.82/3.43  tff(c_1304, plain, (![B_170, B_171, A_172]: (r1_tarski(k3_xboole_0(B_170, k3_xboole_0(B_171, A_172)), A_172))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1209])).
% 8.82/3.43  tff(c_1568, plain, (![B_181]: (r1_tarski(k3_xboole_0(B_181, k2_tarski('#skF_5', '#skF_6')), k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_1304])).
% 8.82/3.43  tff(c_1582, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1568])).
% 8.82/3.43  tff(c_20, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.82/3.43  tff(c_1717, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_1582, c_20])).
% 8.82/3.43  tff(c_24, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.82/3.43  tff(c_26, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.82/3.43  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.82/3.43  tff(c_349, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, k3_xboole_0(A_113, B_114)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.82/3.43  tff(c_423, plain, (![A_122, B_123]: (~r1_xboole_0(A_122, B_123) | k3_xboole_0(A_122, B_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_349])).
% 8.82/3.43  tff(c_427, plain, (![A_26]: (k3_xboole_0(A_26, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_423])).
% 8.82/3.43  tff(c_480, plain, (![A_125, B_126]: (k5_xboole_0(A_125, k3_xboole_0(A_125, B_126))=k4_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.82/3.43  tff(c_489, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=k4_xboole_0(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_427, c_480])).
% 8.82/3.43  tff(c_587, plain, (![A_129]: (k4_xboole_0(A_129, k1_xboole_0)=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_489])).
% 8.82/3.43  tff(c_22, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.82/3.43  tff(c_593, plain, (![A_129]: (k4_xboole_0(A_129, A_129)=k3_xboole_0(A_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_587, c_22])).
% 8.82/3.43  tff(c_601, plain, (![A_129]: (k4_xboole_0(A_129, A_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_593])).
% 8.82/3.43  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.82/3.43  tff(c_504, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_480])).
% 8.82/3.43  tff(c_819, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_601, c_504])).
% 8.82/3.43  tff(c_1391, plain, (![A_177, B_178]: (k3_xboole_0(k3_xboole_0(A_177, B_178), A_177)=k3_xboole_0(A_177, B_178))), inference(resolution, [status(thm)], [c_16, c_200])).
% 8.82/3.43  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.82/3.43  tff(c_1423, plain, (![A_177, B_178]: (k5_xboole_0(k3_xboole_0(A_177, B_178), k3_xboole_0(A_177, B_178))=k4_xboole_0(k3_xboole_0(A_177, B_178), A_177))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_14])).
% 8.82/3.43  tff(c_1513, plain, (![A_179, B_180]: (k4_xboole_0(k3_xboole_0(A_179, B_180), A_179)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_819, c_1423])).
% 8.82/3.43  tff(c_1601, plain, (![B_182, A_183]: (k4_xboole_0(k3_xboole_0(B_182, A_183), A_183)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1513])).
% 8.82/3.43  tff(c_28, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.82/3.43  tff(c_1616, plain, (![A_183, B_182]: (k2_xboole_0(A_183, k3_xboole_0(B_182, A_183))=k5_xboole_0(A_183, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_28])).
% 8.82/3.43  tff(c_1654, plain, (![A_183, B_182]: (k2_xboole_0(A_183, k3_xboole_0(B_182, A_183))=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1616])).
% 8.82/3.43  tff(c_4707, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1717, c_1654])).
% 8.82/3.43  tff(c_60, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.82/3.43  tff(c_56, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.82/3.43  tff(c_1777, plain, (![A_188, B_189, C_190, D_191]: (k2_xboole_0(k2_tarski(A_188, B_189), k2_tarski(C_190, D_191))=k2_enumset1(A_188, B_189, C_190, D_191))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.82/3.43  tff(c_1806, plain, (![A_40, C_190, D_191]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(C_190, D_191))=k2_enumset1(A_40, A_40, C_190, D_191))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1777])).
% 8.82/3.43  tff(c_1812, plain, (![A_40, C_190, D_191]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(C_190, D_191))=k1_enumset1(A_40, C_190, D_191))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1806])).
% 8.82/3.43  tff(c_7518, plain, (![A_349, B_350, A_351]: (k2_xboole_0(k2_tarski(A_349, B_350), k1_tarski(A_351))=k2_enumset1(A_349, B_350, A_351, A_351))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1777])).
% 8.82/3.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.82/3.43  tff(c_7535, plain, (![A_351, A_349, B_350]: (k2_xboole_0(k1_tarski(A_351), k2_tarski(A_349, B_350))=k2_enumset1(A_349, B_350, A_351, A_351))), inference(superposition, [status(thm), theory('equality')], [c_7518, c_2])).
% 8.82/3.43  tff(c_7566, plain, (![A_349, B_350, A_351]: (k2_enumset1(A_349, B_350, A_351, A_351)=k1_enumset1(A_351, A_349, B_350))), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_7535])).
% 8.82/3.43  tff(c_1809, plain, (![A_188, B_189, A_40]: (k2_xboole_0(k2_tarski(A_188, B_189), k1_tarski(A_40))=k2_enumset1(A_188, B_189, A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1777])).
% 8.82/3.43  tff(c_7715, plain, (![A_188, B_189, A_40]: (k2_xboole_0(k2_tarski(A_188, B_189), k1_tarski(A_40))=k1_enumset1(A_40, A_188, B_189))), inference(demodulation, [status(thm), theory('equality')], [c_7566, c_1809])).
% 8.82/3.43  tff(c_16588, plain, (k1_enumset1('#skF_5', '#skF_7', '#skF_8')=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4707, c_7715])).
% 8.82/3.43  tff(c_36, plain, (![E_35, B_30, C_31]: (r2_hidden(E_35, k1_enumset1(E_35, B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.82/3.43  tff(c_17292, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16588, c_36])).
% 8.82/3.43  tff(c_58, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.82/3.43  tff(c_1366, plain, (![E_173, C_174, B_175, A_176]: (E_173=C_174 | E_173=B_175 | E_173=A_176 | ~r2_hidden(E_173, k1_enumset1(A_176, B_175, C_174)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.82/3.43  tff(c_1369, plain, (![E_173, B_42, A_41]: (E_173=B_42 | E_173=A_41 | E_173=A_41 | ~r2_hidden(E_173, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1366])).
% 8.82/3.43  tff(c_17310, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_17292, c_1369])).
% 8.82/3.43  tff(c_17314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_74, c_72, c_17310])).
% 8.82/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.82/3.43  
% 8.82/3.43  Inference rules
% 8.82/3.43  ----------------------
% 8.82/3.43  #Ref     : 0
% 8.82/3.43  #Sup     : 4083
% 8.82/3.43  #Fact    : 18
% 8.82/3.43  #Define  : 0
% 8.82/3.43  #Split   : 3
% 8.82/3.43  #Chain   : 0
% 8.82/3.43  #Close   : 0
% 8.82/3.43  
% 8.82/3.43  Ordering : KBO
% 8.82/3.43  
% 8.82/3.43  Simplification rules
% 8.82/3.43  ----------------------
% 8.82/3.43  #Subsume      : 207
% 8.82/3.43  #Demod        : 4606
% 8.82/3.43  #Tautology    : 2972
% 8.82/3.43  #SimpNegUnit  : 9
% 8.82/3.43  #BackRed      : 2
% 8.82/3.43  
% 8.82/3.43  #Partial instantiations: 0
% 8.82/3.43  #Strategies tried      : 1
% 8.82/3.43  
% 8.82/3.43  Timing (in seconds)
% 8.82/3.43  ----------------------
% 8.82/3.43  Preprocessing        : 0.33
% 8.82/3.43  Parsing              : 0.17
% 8.82/3.43  CNF conversion       : 0.03
% 8.82/3.43  Main loop            : 2.32
% 8.82/3.43  Inferencing          : 0.54
% 8.82/3.43  Reduction            : 1.22
% 8.82/3.43  Demodulation         : 1.04
% 8.82/3.43  BG Simplification    : 0.06
% 8.82/3.43  Subsumption          : 0.39
% 8.82/3.43  Abstraction          : 0.10
% 8.82/3.43  MUC search           : 0.00
% 8.82/3.43  Cooper               : 0.00
% 8.82/3.43  Total                : 2.69
% 8.82/3.43  Index Insertion      : 0.00
% 8.82/3.43  Index Deletion       : 0.00
% 8.82/3.43  Index Matching       : 0.00
% 8.82/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
