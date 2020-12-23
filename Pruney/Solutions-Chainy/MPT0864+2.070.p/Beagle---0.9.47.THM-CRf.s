%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 194 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 394 expanded)
%              Number of equality atoms :   66 ( 224 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_46,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_3'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_604,plain,(
    ! [D_114,A_115,B_116] :
      ( r2_hidden(D_114,A_115)
      | ~ r2_hidden(D_114,k4_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_779,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_149,B_150)),A_149)
      | k4_xboole_0(A_149,B_150) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_604])).

tff(c_577,plain,(
    ! [D_108,B_109,A_110] :
      ( ~ r2_hidden(D_108,B_109)
      | ~ r2_hidden(D_108,k4_xboole_0(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_582,plain,(
    ! [A_110,B_109] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_110,B_109)),B_109)
      | k4_xboole_0(A_110,B_109) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_577])).

tff(c_810,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_779,c_582])).

tff(c_30,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_817,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_30])).

tff(c_611,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(k1_tarski(A_117),k1_tarski(B_118)) = k1_tarski(A_117)
      | B_118 = A_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_635,plain,(
    ! [B_119,A_120] :
      ( ~ r2_hidden(B_119,k1_tarski(A_120))
      | B_119 = A_120 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_36])).

tff(c_640,plain,(
    ! [A_120] :
      ( '#skF_3'(k1_tarski(A_120)) = A_120
      | k1_tarski(A_120) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_635])).

tff(c_859,plain,(
    ! [A_120] : '#skF_3'(k1_tarski(A_120)) = A_120 ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_640])).

tff(c_873,plain,(
    ! [A_154] : '#skF_3'(k1_tarski(A_154)) = A_154 ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_640])).

tff(c_663,plain,(
    ! [D_125,A_126,C_127] :
      ( ~ r2_hidden(D_125,A_126)
      | k4_tarski(C_127,D_125) != '#skF_3'(A_126)
      | k1_xboole_0 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_666,plain,(
    ! [C_127,A_26] :
      ( k4_tarski(C_127,'#skF_3'(A_26)) != '#skF_3'(A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(resolution,[status(thm)],[c_46,c_663])).

tff(c_888,plain,(
    ! [C_127,A_154] :
      ( k4_tarski(C_127,A_154) != '#skF_3'(k1_tarski(A_154))
      | k1_tarski(A_154) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_666])).

tff(c_902,plain,(
    ! [C_127,A_154] :
      ( k4_tarski(C_127,A_154) != A_154
      | k1_tarski(A_154) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_888])).

tff(c_903,plain,(
    ! [C_127,A_154] : k4_tarski(C_127,A_154) != A_154 ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_902])).

tff(c_167,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,A_54)
      | ~ r2_hidden(D_53,k4_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_329,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_88,B_89)),A_88)
      | k4_xboole_0(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_185,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [A_60,B_59] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_60,B_59)),B_59)
      | k4_xboole_0(A_60,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_185])).

tff(c_355,plain,(
    ! [A_88] : k4_xboole_0(A_88,A_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_329,c_190])).

tff(c_363,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_30])).

tff(c_201,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(k1_tarski(A_62),k1_tarski(B_63)) = k1_tarski(A_62)
      | B_63 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_225,plain,(
    ! [B_64,A_65] :
      ( ~ r2_hidden(B_64,k1_tarski(A_65))
      | B_64 = A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_36])).

tff(c_230,plain,(
    ! [A_65] :
      ( '#skF_3'(k1_tarski(A_65)) = A_65
      | k1_tarski(A_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_225])).

tff(c_437,plain,(
    ! [A_65] : '#skF_3'(k1_tarski(A_65)) = A_65 ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_230])).

tff(c_467,plain,(
    ! [A_100] : '#skF_3'(k1_tarski(A_100)) = A_100 ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_230])).

tff(c_261,plain,(
    ! [C_75,A_76,D_77] :
      ( ~ r2_hidden(C_75,A_76)
      | k4_tarski(C_75,D_77) != '#skF_3'(A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_264,plain,(
    ! [A_26,D_77] :
      ( k4_tarski('#skF_3'(A_26),D_77) != '#skF_3'(A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(resolution,[status(thm)],[c_46,c_261])).

tff(c_479,plain,(
    ! [A_100,D_77] :
      ( k4_tarski(A_100,D_77) != '#skF_3'(k1_tarski(A_100))
      | k1_tarski(A_100) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_264])).

tff(c_494,plain,(
    ! [A_100,D_77] :
      ( k4_tarski(A_100,D_77) != A_100
      | k1_tarski(A_100) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_479])).

tff(c_495,plain,(
    ! [A_100,D_77] : k4_tarski(A_100,D_77) != A_100 ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_494])).

tff(c_54,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_93,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_93])).

tff(c_77,plain,(
    ! [A_40,B_41] : k2_mcart_1(k4_tarski(A_40,B_41)) = B_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_52,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_111,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_52])).

tff(c_112,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_114,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_54])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_114])).

tff(c_521,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_524,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_54])).

tff(c_978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.61/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.61/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.39  
% 2.85/1.40  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.85/1.40  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.85/1.40  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.85/1.40  tff(f_57, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.85/1.40  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.85/1.40  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.85/1.40  tff(c_46, plain, (![A_26]: (r2_hidden('#skF_3'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.40  tff(c_604, plain, (![D_114, A_115, B_116]: (r2_hidden(D_114, A_115) | ~r2_hidden(D_114, k4_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_779, plain, (![A_149, B_150]: (r2_hidden('#skF_3'(k4_xboole_0(A_149, B_150)), A_149) | k4_xboole_0(A_149, B_150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_604])).
% 2.85/1.40  tff(c_577, plain, (![D_108, B_109, A_110]: (~r2_hidden(D_108, B_109) | ~r2_hidden(D_108, k4_xboole_0(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_582, plain, (![A_110, B_109]: (~r2_hidden('#skF_3'(k4_xboole_0(A_110, B_109)), B_109) | k4_xboole_0(A_110, B_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_577])).
% 2.85/1.40  tff(c_810, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_779, c_582])).
% 2.85/1.40  tff(c_30, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.40  tff(c_817, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_810, c_30])).
% 2.85/1.40  tff(c_611, plain, (![A_117, B_118]: (k4_xboole_0(k1_tarski(A_117), k1_tarski(B_118))=k1_tarski(A_117) | B_118=A_117)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.40  tff(c_36, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.40  tff(c_635, plain, (![B_119, A_120]: (~r2_hidden(B_119, k1_tarski(A_120)) | B_119=A_120)), inference(superposition, [status(thm), theory('equality')], [c_611, c_36])).
% 2.85/1.40  tff(c_640, plain, (![A_120]: ('#skF_3'(k1_tarski(A_120))=A_120 | k1_tarski(A_120)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_635])).
% 2.85/1.40  tff(c_859, plain, (![A_120]: ('#skF_3'(k1_tarski(A_120))=A_120)), inference(negUnitSimplification, [status(thm)], [c_817, c_640])).
% 2.85/1.40  tff(c_873, plain, (![A_154]: ('#skF_3'(k1_tarski(A_154))=A_154)), inference(negUnitSimplification, [status(thm)], [c_817, c_640])).
% 2.85/1.40  tff(c_663, plain, (![D_125, A_126, C_127]: (~r2_hidden(D_125, A_126) | k4_tarski(C_127, D_125)!='#skF_3'(A_126) | k1_xboole_0=A_126)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.40  tff(c_666, plain, (![C_127, A_26]: (k4_tarski(C_127, '#skF_3'(A_26))!='#skF_3'(A_26) | k1_xboole_0=A_26)), inference(resolution, [status(thm)], [c_46, c_663])).
% 2.85/1.40  tff(c_888, plain, (![C_127, A_154]: (k4_tarski(C_127, A_154)!='#skF_3'(k1_tarski(A_154)) | k1_tarski(A_154)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_873, c_666])).
% 2.85/1.40  tff(c_902, plain, (![C_127, A_154]: (k4_tarski(C_127, A_154)!=A_154 | k1_tarski(A_154)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_859, c_888])).
% 2.85/1.40  tff(c_903, plain, (![C_127, A_154]: (k4_tarski(C_127, A_154)!=A_154)), inference(negUnitSimplification, [status(thm)], [c_817, c_902])).
% 2.85/1.40  tff(c_167, plain, (![D_53, A_54, B_55]: (r2_hidden(D_53, A_54) | ~r2_hidden(D_53, k4_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_329, plain, (![A_88, B_89]: (r2_hidden('#skF_3'(k4_xboole_0(A_88, B_89)), A_88) | k4_xboole_0(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_167])).
% 2.85/1.40  tff(c_185, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k4_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.40  tff(c_190, plain, (![A_60, B_59]: (~r2_hidden('#skF_3'(k4_xboole_0(A_60, B_59)), B_59) | k4_xboole_0(A_60, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_185])).
% 2.85/1.40  tff(c_355, plain, (![A_88]: (k4_xboole_0(A_88, A_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_329, c_190])).
% 2.85/1.40  tff(c_363, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_355, c_30])).
% 2.85/1.40  tff(c_201, plain, (![A_62, B_63]: (k4_xboole_0(k1_tarski(A_62), k1_tarski(B_63))=k1_tarski(A_62) | B_63=A_62)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.40  tff(c_225, plain, (![B_64, A_65]: (~r2_hidden(B_64, k1_tarski(A_65)) | B_64=A_65)), inference(superposition, [status(thm), theory('equality')], [c_201, c_36])).
% 2.85/1.40  tff(c_230, plain, (![A_65]: ('#skF_3'(k1_tarski(A_65))=A_65 | k1_tarski(A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_225])).
% 2.85/1.40  tff(c_437, plain, (![A_65]: ('#skF_3'(k1_tarski(A_65))=A_65)), inference(negUnitSimplification, [status(thm)], [c_363, c_230])).
% 2.85/1.40  tff(c_467, plain, (![A_100]: ('#skF_3'(k1_tarski(A_100))=A_100)), inference(negUnitSimplification, [status(thm)], [c_363, c_230])).
% 2.85/1.40  tff(c_261, plain, (![C_75, A_76, D_77]: (~r2_hidden(C_75, A_76) | k4_tarski(C_75, D_77)!='#skF_3'(A_76) | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.40  tff(c_264, plain, (![A_26, D_77]: (k4_tarski('#skF_3'(A_26), D_77)!='#skF_3'(A_26) | k1_xboole_0=A_26)), inference(resolution, [status(thm)], [c_46, c_261])).
% 2.85/1.40  tff(c_479, plain, (![A_100, D_77]: (k4_tarski(A_100, D_77)!='#skF_3'(k1_tarski(A_100)) | k1_tarski(A_100)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_467, c_264])).
% 2.85/1.40  tff(c_494, plain, (![A_100, D_77]: (k4_tarski(A_100, D_77)!=A_100 | k1_tarski(A_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_479])).
% 2.85/1.40  tff(c_495, plain, (![A_100, D_77]: (k4_tarski(A_100, D_77)!=A_100)), inference(negUnitSimplification, [status(thm)], [c_363, c_494])).
% 2.85/1.40  tff(c_54, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.40  tff(c_93, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.85/1.40  tff(c_102, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_54, c_93])).
% 2.85/1.40  tff(c_77, plain, (![A_40, B_41]: (k2_mcart_1(k4_tarski(A_40, B_41))=B_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.85/1.40  tff(c_86, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_54, c_77])).
% 2.85/1.40  tff(c_52, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.40  tff(c_111, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_52])).
% 2.85/1.40  tff(c_112, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_111])).
% 2.85/1.40  tff(c_114, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_54])).
% 2.85/1.40  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_114])).
% 2.85/1.40  tff(c_521, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_111])).
% 2.85/1.40  tff(c_524, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_54])).
% 2.85/1.40  tff(c_978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_524])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  Inference rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Ref     : 0
% 2.85/1.40  #Sup     : 223
% 2.85/1.40  #Fact    : 0
% 2.85/1.40  #Define  : 0
% 2.85/1.40  #Split   : 1
% 2.85/1.40  #Chain   : 0
% 2.85/1.40  #Close   : 0
% 2.85/1.40  
% 2.85/1.40  Ordering : KBO
% 2.85/1.40  
% 2.85/1.40  Simplification rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Subsume      : 18
% 2.85/1.40  #Demod        : 33
% 2.85/1.40  #Tautology    : 108
% 2.85/1.40  #SimpNegUnit  : 16
% 2.85/1.40  #BackRed      : 12
% 2.85/1.40  
% 2.85/1.40  #Partial instantiations: 0
% 2.85/1.40  #Strategies tried      : 1
% 2.85/1.40  
% 2.85/1.40  Timing (in seconds)
% 2.85/1.40  ----------------------
% 2.85/1.41  Preprocessing        : 0.30
% 2.85/1.41  Parsing              : 0.15
% 2.85/1.41  CNF conversion       : 0.02
% 2.85/1.41  Main loop            : 0.35
% 2.85/1.41  Inferencing          : 0.13
% 2.85/1.41  Reduction            : 0.09
% 2.85/1.41  Demodulation         : 0.06
% 2.85/1.41  BG Simplification    : 0.02
% 2.85/1.41  Subsumption          : 0.06
% 2.85/1.41  Abstraction          : 0.02
% 2.85/1.41  MUC search           : 0.00
% 2.85/1.41  Cooper               : 0.00
% 2.85/1.41  Total                : 0.68
% 2.85/1.41  Index Insertion      : 0.00
% 2.85/1.41  Index Deletion       : 0.00
% 2.85/1.41  Index Matching       : 0.00
% 2.85/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
