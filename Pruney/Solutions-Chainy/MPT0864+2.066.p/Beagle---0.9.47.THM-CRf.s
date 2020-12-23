%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 234 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 388 expanded)
%              Number of equality atoms :   77 ( 258 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_62,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_3'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1063,plain,(
    ! [D_171,B_172,A_173] :
      ( r2_hidden(D_171,B_172)
      | ~ r2_hidden(D_171,k3_xboole_0(A_173,B_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1687,plain,(
    ! [A_236,B_237] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_236,B_237)),B_237)
      | k3_xboole_0(A_236,B_237) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_1063])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1373,plain,(
    ! [B_210,C_211,A_212] :
      ( ~ r2_hidden(B_210,C_211)
      | k4_xboole_0(k2_tarski(A_212,B_210),C_211) != k2_tarski(A_212,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1400,plain,(
    ! [B_210] : ~ r2_hidden(B_210,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1373])).

tff(c_1728,plain,(
    ! [A_236] : k3_xboole_0(A_236,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1687,c_1400])).

tff(c_1072,plain,(
    ! [A_174,B_175] : k4_xboole_0(A_174,k4_xboole_0(A_174,B_175)) = k3_xboole_0(A_174,B_175) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1087,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1072])).

tff(c_42,plain,(
    ! [B_43] : k4_xboole_0(k1_tarski(B_43),k1_tarski(B_43)) != k1_tarski(B_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1113,plain,(
    ! [B_43] : k3_xboole_0(k1_tarski(B_43),k1_xboole_0) != k1_tarski(B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_42])).

tff(c_1770,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_1113])).

tff(c_1215,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(k1_tarski(A_187),k1_tarski(B_188)) = k1_tarski(A_187)
      | B_188 = A_187 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [B_45,A_44] :
      ( ~ r2_hidden(B_45,A_44)
      | k4_xboole_0(A_44,k1_tarski(B_45)) != A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1260,plain,(
    ! [B_192,A_193] :
      ( ~ r2_hidden(B_192,k1_tarski(A_193))
      | B_192 = A_193 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_46])).

tff(c_1270,plain,(
    ! [A_193] :
      ( '#skF_3'(k1_tarski(A_193)) = A_193
      | k1_tarski(A_193) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_1260])).

tff(c_1826,plain,(
    ! [A_193] : '#skF_3'(k1_tarski(A_193)) = A_193 ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1270])).

tff(c_1910,plain,(
    ! [A_245] : '#skF_3'(k1_tarski(A_245)) = A_245 ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1270])).

tff(c_1253,plain,(
    ! [D_189,A_190,C_191] :
      ( ~ r2_hidden(D_189,A_190)
      | k4_tarski(C_191,D_189) != '#skF_3'(A_190)
      | k1_xboole_0 = A_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1259,plain,(
    ! [C_191,A_53] :
      ( k4_tarski(C_191,'#skF_3'(A_53)) != '#skF_3'(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_62,c_1253])).

tff(c_1919,plain,(
    ! [C_191,A_245] :
      ( k4_tarski(C_191,A_245) != '#skF_3'(k1_tarski(A_245))
      | k1_tarski(A_245) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_1259])).

tff(c_1929,plain,(
    ! [C_191,A_245] :
      ( k4_tarski(C_191,A_245) != A_245
      | k1_tarski(A_245) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_1919])).

tff(c_1930,plain,(
    ! [C_191,A_245] : k4_tarski(C_191,A_245) != A_245 ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1929])).

tff(c_214,plain,(
    ! [D_84,B_85,A_86] :
      ( r2_hidden(D_84,B_85)
      | ~ r2_hidden(D_84,k3_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_222,plain,(
    ! [A_86,B_85] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_86,B_85)),B_85)
      | k3_xboole_0(A_86,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_568,plain,(
    ! [B_132,C_133,A_134] :
      ( ~ r2_hidden(B_132,C_133)
      | k4_xboole_0(k2_tarski(A_134,B_132),C_133) != k2_tarski(A_134,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_600,plain,(
    ! [B_135] : ~ r2_hidden(B_135,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_568])).

tff(c_614,plain,(
    ! [A_86] : k3_xboole_0(A_86,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_222,c_600])).

tff(c_250,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_268,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_250])).

tff(c_304,plain,(
    ! [B_43] : k3_xboole_0(k1_tarski(B_43),k1_xboole_0) != k1_tarski(B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_42])).

tff(c_680,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_304])).

tff(c_272,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),k1_tarski(B_96)) = k1_tarski(A_95)
      | B_96 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_354,plain,(
    ! [B_98,A_99] :
      ( ~ r2_hidden(B_98,k1_tarski(A_99))
      | B_98 = A_99 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_46])).

tff(c_364,plain,(
    ! [A_99] :
      ( '#skF_3'(k1_tarski(A_99)) = A_99
      | k1_tarski(A_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_354])).

tff(c_758,plain,(
    ! [A_99] : '#skF_3'(k1_tarski(A_99)) = A_99 ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_364])).

tff(c_826,plain,(
    ! [A_144] : '#skF_3'(k1_tarski(A_144)) = A_144 ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_364])).

tff(c_455,plain,(
    ! [C_115,A_116,D_117] :
      ( ~ r2_hidden(C_115,A_116)
      | k4_tarski(C_115,D_117) != '#skF_3'(A_116)
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_461,plain,(
    ! [A_53,D_117] :
      ( k4_tarski('#skF_3'(A_53),D_117) != '#skF_3'(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_62,c_455])).

tff(c_832,plain,(
    ! [A_144,D_117] :
      ( k4_tarski(A_144,D_117) != '#skF_3'(k1_tarski(A_144))
      | k1_tarski(A_144) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_461])).

tff(c_843,plain,(
    ! [A_144,D_117] :
      ( k4_tarski(A_144,D_117) != A_144
      | k1_tarski(A_144) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_832])).

tff(c_844,plain,(
    ! [A_144,D_117] : k4_tarski(A_144,D_117) != A_144 ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_843])).

tff(c_70,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_114,plain,(
    ! [A_70,B_71] : k1_mcart_1(k4_tarski(A_70,B_71)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_123,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_114])).

tff(c_102,plain,(
    ! [A_68,B_69] : k2_mcart_1(k4_tarski(A_68,B_69)) = B_69 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_111,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_102])).

tff(c_68,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_135,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_111,c_68])).

tff(c_136,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_138,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_70])).

tff(c_975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_138])).

tff(c_976,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_979,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_70])).

tff(c_1963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1930,c_979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:32:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.56  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.32/1.56  
% 3.32/1.56  %Foreground sorts:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Background operators:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Foreground operators:
% 3.32/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.32/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.32/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.32/1.56  
% 3.39/1.57  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.39/1.57  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.39/1.57  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.39/1.57  tff(f_74, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.39/1.57  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.39/1.57  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.39/1.57  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.39/1.57  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.39/1.57  tff(f_80, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.39/1.57  tff(c_62, plain, (![A_53]: (r2_hidden('#skF_3'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.39/1.57  tff(c_1063, plain, (![D_171, B_172, A_173]: (r2_hidden(D_171, B_172) | ~r2_hidden(D_171, k3_xboole_0(A_173, B_172)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.39/1.57  tff(c_1687, plain, (![A_236, B_237]: (r2_hidden('#skF_3'(k3_xboole_0(A_236, B_237)), B_237) | k3_xboole_0(A_236, B_237)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_1063])).
% 3.39/1.57  tff(c_24, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.57  tff(c_1373, plain, (![B_210, C_211, A_212]: (~r2_hidden(B_210, C_211) | k4_xboole_0(k2_tarski(A_212, B_210), C_211)!=k2_tarski(A_212, B_210))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.57  tff(c_1400, plain, (![B_210]: (~r2_hidden(B_210, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1373])).
% 3.39/1.57  tff(c_1728, plain, (![A_236]: (k3_xboole_0(A_236, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1687, c_1400])).
% 3.39/1.57  tff(c_1072, plain, (![A_174, B_175]: (k4_xboole_0(A_174, k4_xboole_0(A_174, B_175))=k3_xboole_0(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.57  tff(c_1087, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1072])).
% 3.39/1.57  tff(c_42, plain, (![B_43]: (k4_xboole_0(k1_tarski(B_43), k1_tarski(B_43))!=k1_tarski(B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.57  tff(c_1113, plain, (![B_43]: (k3_xboole_0(k1_tarski(B_43), k1_xboole_0)!=k1_tarski(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_42])).
% 3.39/1.57  tff(c_1770, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1728, c_1113])).
% 3.39/1.57  tff(c_1215, plain, (![A_187, B_188]: (k4_xboole_0(k1_tarski(A_187), k1_tarski(B_188))=k1_tarski(A_187) | B_188=A_187)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.57  tff(c_46, plain, (![B_45, A_44]: (~r2_hidden(B_45, A_44) | k4_xboole_0(A_44, k1_tarski(B_45))!=A_44)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.39/1.57  tff(c_1260, plain, (![B_192, A_193]: (~r2_hidden(B_192, k1_tarski(A_193)) | B_192=A_193)), inference(superposition, [status(thm), theory('equality')], [c_1215, c_46])).
% 3.39/1.57  tff(c_1270, plain, (![A_193]: ('#skF_3'(k1_tarski(A_193))=A_193 | k1_tarski(A_193)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_1260])).
% 3.39/1.57  tff(c_1826, plain, (![A_193]: ('#skF_3'(k1_tarski(A_193))=A_193)), inference(negUnitSimplification, [status(thm)], [c_1770, c_1270])).
% 3.39/1.57  tff(c_1910, plain, (![A_245]: ('#skF_3'(k1_tarski(A_245))=A_245)), inference(negUnitSimplification, [status(thm)], [c_1770, c_1270])).
% 3.39/1.57  tff(c_1253, plain, (![D_189, A_190, C_191]: (~r2_hidden(D_189, A_190) | k4_tarski(C_191, D_189)!='#skF_3'(A_190) | k1_xboole_0=A_190)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.39/1.57  tff(c_1259, plain, (![C_191, A_53]: (k4_tarski(C_191, '#skF_3'(A_53))!='#skF_3'(A_53) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_62, c_1253])).
% 3.39/1.57  tff(c_1919, plain, (![C_191, A_245]: (k4_tarski(C_191, A_245)!='#skF_3'(k1_tarski(A_245)) | k1_tarski(A_245)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1910, c_1259])).
% 3.39/1.57  tff(c_1929, plain, (![C_191, A_245]: (k4_tarski(C_191, A_245)!=A_245 | k1_tarski(A_245)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_1919])).
% 3.39/1.57  tff(c_1930, plain, (![C_191, A_245]: (k4_tarski(C_191, A_245)!=A_245)), inference(negUnitSimplification, [status(thm)], [c_1770, c_1929])).
% 3.39/1.57  tff(c_214, plain, (![D_84, B_85, A_86]: (r2_hidden(D_84, B_85) | ~r2_hidden(D_84, k3_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.39/1.57  tff(c_222, plain, (![A_86, B_85]: (r2_hidden('#skF_3'(k3_xboole_0(A_86, B_85)), B_85) | k3_xboole_0(A_86, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_214])).
% 3.39/1.57  tff(c_568, plain, (![B_132, C_133, A_134]: (~r2_hidden(B_132, C_133) | k4_xboole_0(k2_tarski(A_134, B_132), C_133)!=k2_tarski(A_134, B_132))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.57  tff(c_600, plain, (![B_135]: (~r2_hidden(B_135, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_568])).
% 3.39/1.57  tff(c_614, plain, (![A_86]: (k3_xboole_0(A_86, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_222, c_600])).
% 3.39/1.57  tff(c_250, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.57  tff(c_268, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_250])).
% 3.39/1.57  tff(c_304, plain, (![B_43]: (k3_xboole_0(k1_tarski(B_43), k1_xboole_0)!=k1_tarski(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_42])).
% 3.39/1.57  tff(c_680, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_614, c_304])).
% 3.39/1.57  tff(c_272, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), k1_tarski(B_96))=k1_tarski(A_95) | B_96=A_95)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.57  tff(c_354, plain, (![B_98, A_99]: (~r2_hidden(B_98, k1_tarski(A_99)) | B_98=A_99)), inference(superposition, [status(thm), theory('equality')], [c_272, c_46])).
% 3.39/1.57  tff(c_364, plain, (![A_99]: ('#skF_3'(k1_tarski(A_99))=A_99 | k1_tarski(A_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_354])).
% 3.39/1.57  tff(c_758, plain, (![A_99]: ('#skF_3'(k1_tarski(A_99))=A_99)), inference(negUnitSimplification, [status(thm)], [c_680, c_364])).
% 3.39/1.57  tff(c_826, plain, (![A_144]: ('#skF_3'(k1_tarski(A_144))=A_144)), inference(negUnitSimplification, [status(thm)], [c_680, c_364])).
% 3.39/1.57  tff(c_455, plain, (![C_115, A_116, D_117]: (~r2_hidden(C_115, A_116) | k4_tarski(C_115, D_117)!='#skF_3'(A_116) | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.39/1.57  tff(c_461, plain, (![A_53, D_117]: (k4_tarski('#skF_3'(A_53), D_117)!='#skF_3'(A_53) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_62, c_455])).
% 3.39/1.57  tff(c_832, plain, (![A_144, D_117]: (k4_tarski(A_144, D_117)!='#skF_3'(k1_tarski(A_144)) | k1_tarski(A_144)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_826, c_461])).
% 3.39/1.57  tff(c_843, plain, (![A_144, D_117]: (k4_tarski(A_144, D_117)!=A_144 | k1_tarski(A_144)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_758, c_832])).
% 3.39/1.57  tff(c_844, plain, (![A_144, D_117]: (k4_tarski(A_144, D_117)!=A_144)), inference(negUnitSimplification, [status(thm)], [c_680, c_843])).
% 3.39/1.57  tff(c_70, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.39/1.57  tff(c_114, plain, (![A_70, B_71]: (k1_mcart_1(k4_tarski(A_70, B_71))=A_70)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.57  tff(c_123, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_70, c_114])).
% 3.39/1.57  tff(c_102, plain, (![A_68, B_69]: (k2_mcart_1(k4_tarski(A_68, B_69))=B_69)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.57  tff(c_111, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_70, c_102])).
% 3.39/1.57  tff(c_68, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.39/1.57  tff(c_135, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_111, c_68])).
% 3.39/1.57  tff(c_136, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_135])).
% 3.39/1.57  tff(c_138, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_70])).
% 3.39/1.57  tff(c_975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_138])).
% 3.39/1.57  tff(c_976, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_135])).
% 3.39/1.57  tff(c_979, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_976, c_70])).
% 3.39/1.57  tff(c_1963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1930, c_979])).
% 3.39/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  Inference rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Ref     : 0
% 3.39/1.57  #Sup     : 427
% 3.39/1.57  #Fact    : 0
% 3.39/1.57  #Define  : 0
% 3.39/1.57  #Split   : 1
% 3.39/1.57  #Chain   : 0
% 3.39/1.57  #Close   : 0
% 3.39/1.57  
% 3.39/1.57  Ordering : KBO
% 3.39/1.57  
% 3.39/1.57  Simplification rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Subsume      : 47
% 3.39/1.57  #Demod        : 153
% 3.39/1.57  #Tautology    : 261
% 3.39/1.57  #SimpNegUnit  : 45
% 3.39/1.57  #BackRed      : 28
% 3.39/1.57  
% 3.39/1.57  #Partial instantiations: 0
% 3.39/1.57  #Strategies tried      : 1
% 3.39/1.58  
% 3.39/1.58  Timing (in seconds)
% 3.39/1.58  ----------------------
% 3.39/1.58  Preprocessing        : 0.34
% 3.39/1.58  Parsing              : 0.18
% 3.39/1.58  CNF conversion       : 0.03
% 3.39/1.58  Main loop            : 0.46
% 3.39/1.58  Inferencing          : 0.17
% 3.39/1.58  Reduction            : 0.14
% 3.39/1.58  Demodulation         : 0.10
% 3.39/1.58  BG Simplification    : 0.03
% 3.39/1.58  Subsumption          : 0.07
% 3.39/1.58  Abstraction          : 0.03
% 3.39/1.58  MUC search           : 0.00
% 3.39/1.58  Cooper               : 0.00
% 3.39/1.58  Total                : 0.83
% 3.39/1.58  Index Insertion      : 0.00
% 3.39/1.58  Index Deletion       : 0.00
% 3.39/1.58  Index Matching       : 0.00
% 3.39/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
