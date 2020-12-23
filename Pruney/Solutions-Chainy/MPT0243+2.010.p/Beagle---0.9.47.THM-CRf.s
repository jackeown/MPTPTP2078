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
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 206 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 406 expanded)
%              Number of equality atoms :   31 (  80 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_48,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [A_49,B_50] : r2_hidden(A_49,k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_100,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden(A_66,B_67)
      | ~ r1_tarski(k2_tarski(A_66,B_68),B_67) ) ),
    inference(resolution,[status(thm)],[c_67,c_100])).

tff(c_126,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_119])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_126])).

tff(c_134,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_133,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [B_50,A_49] : r2_hidden(B_50,k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_10])).

tff(c_142,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    ! [B_76,B_77,A_78] :
      ( r2_hidden(B_76,B_77)
      | ~ r1_tarski(k2_tarski(A_78,B_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_64,c_142])).

tff(c_188,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_181])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_188])).

tff(c_196,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_44,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_328,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_196,c_44])).

tff(c_46,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_135])).

tff(c_138,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_198,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_138])).

tff(c_195,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_352,plain,(
    ! [E_119,C_120,B_121,A_122] :
      ( E_119 = C_120
      | E_119 = B_121
      | E_119 = A_122
      | ~ r2_hidden(E_119,k1_enumset1(A_122,B_121,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [E_126,B_127,A_128] :
      ( E_126 = B_127
      | E_126 = A_128
      | E_126 = A_128
      | ~ r2_hidden(E_126,k2_tarski(A_128,B_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_352])).

tff(c_551,plain,(
    ! [A_187,B_188,B_189] :
      ( '#skF_1'(k2_tarski(A_187,B_188),B_189) = B_188
      | '#skF_1'(k2_tarski(A_187,B_188),B_189) = A_187
      | r1_tarski(k2_tarski(A_187,B_188),B_189) ) ),
    inference(resolution,[status(thm)],[c_6,c_410])).

tff(c_584,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_551,c_328])).

tff(c_588,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_601,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_4])).

tff(c_611,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_601])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_611])).

tff(c_614,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_628,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_4])).

tff(c_638,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_628])).

tff(c_640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_638])).

tff(c_642,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_729,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_642,c_50])).

tff(c_641,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_643,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_642,c_54])).

tff(c_766,plain,(
    ! [E_230,C_231,B_232,A_233] :
      ( E_230 = C_231
      | E_230 = B_232
      | E_230 = A_233
      | ~ r2_hidden(E_230,k1_enumset1(A_233,B_232,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_805,plain,(
    ! [E_234,B_235,A_236] :
      ( E_234 = B_235
      | E_234 = A_236
      | E_234 = A_236
      | ~ r2_hidden(E_234,k2_tarski(A_236,B_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_766])).

tff(c_882,plain,(
    ! [A_273,B_274,B_275] :
      ( '#skF_1'(k2_tarski(A_273,B_274),B_275) = B_274
      | '#skF_1'(k2_tarski(A_273,B_274),B_275) = A_273
      | r1_tarski(k2_tarski(A_273,B_274),B_275) ) ),
    inference(resolution,[status(thm)],[c_6,c_805])).

tff(c_908,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_882,c_729])).

tff(c_912,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_920,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_4])).

tff(c_928,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_920])).

tff(c_930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_928])).

tff(c_931,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_939,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_4])).

tff(c_947,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_939])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:52:56 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.71/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.44  
% 3.06/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.06/1.45  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.06/1.45  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.06/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.06/1.45  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_90, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_48])).
% 3.06/1.45  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 3.06/1.45  tff(c_58, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.45  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.45  tff(c_67, plain, (![A_49, B_50]: (r2_hidden(A_49, k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_12])).
% 3.06/1.45  tff(c_100, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.45  tff(c_119, plain, (![A_66, B_67, B_68]: (r2_hidden(A_66, B_67) | ~r1_tarski(k2_tarski(A_66, B_68), B_67))), inference(resolution, [status(thm)], [c_67, c_100])).
% 3.06/1.45  tff(c_126, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_119])).
% 3.06/1.45  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_126])).
% 3.06/1.45  tff(c_134, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_48])).
% 3.06/1.45  tff(c_133, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.06/1.45  tff(c_141, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_133])).
% 3.06/1.45  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.45  tff(c_64, plain, (![B_50, A_49]: (r2_hidden(B_50, k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_10])).
% 3.06/1.45  tff(c_142, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.45  tff(c_181, plain, (![B_76, B_77, A_78]: (r2_hidden(B_76, B_77) | ~r1_tarski(k2_tarski(A_78, B_76), B_77))), inference(resolution, [status(thm)], [c_64, c_142])).
% 3.06/1.45  tff(c_188, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_181])).
% 3.06/1.45  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_188])).
% 3.06/1.45  tff(c_196, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_133])).
% 3.06/1.45  tff(c_44, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_328, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_196, c_44])).
% 3.06/1.45  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_135, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_46])).
% 3.06/1.45  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_135])).
% 3.06/1.45  tff(c_138, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 3.06/1.45  tff(c_198, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_138])).
% 3.06/1.45  tff(c_195, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_133])).
% 3.06/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.45  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.45  tff(c_352, plain, (![E_119, C_120, B_121, A_122]: (E_119=C_120 | E_119=B_121 | E_119=A_122 | ~r2_hidden(E_119, k1_enumset1(A_122, B_121, C_120)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.45  tff(c_410, plain, (![E_126, B_127, A_128]: (E_126=B_127 | E_126=A_128 | E_126=A_128 | ~r2_hidden(E_126, k2_tarski(A_128, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_352])).
% 3.06/1.45  tff(c_551, plain, (![A_187, B_188, B_189]: ('#skF_1'(k2_tarski(A_187, B_188), B_189)=B_188 | '#skF_1'(k2_tarski(A_187, B_188), B_189)=A_187 | r1_tarski(k2_tarski(A_187, B_188), B_189))), inference(resolution, [status(thm)], [c_6, c_410])).
% 3.06/1.45  tff(c_584, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5' | '#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_551, c_328])).
% 3.06/1.45  tff(c_588, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_584])).
% 3.06/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.45  tff(c_601, plain, (~r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_588, c_4])).
% 3.06/1.45  tff(c_611, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_601])).
% 3.06/1.45  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_611])).
% 3.06/1.45  tff(c_614, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_584])).
% 3.06/1.45  tff(c_628, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_614, c_4])).
% 3.06/1.45  tff(c_638, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_628])).
% 3.06/1.45  tff(c_640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_638])).
% 3.06/1.45  tff(c_642, plain, (~r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 3.06/1.45  tff(c_50, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_729, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_642, c_50])).
% 3.06/1.45  tff(c_641, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 3.06/1.45  tff(c_54, plain, (r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.45  tff(c_643, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_642, c_54])).
% 3.06/1.45  tff(c_766, plain, (![E_230, C_231, B_232, A_233]: (E_230=C_231 | E_230=B_232 | E_230=A_233 | ~r2_hidden(E_230, k1_enumset1(A_233, B_232, C_231)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.45  tff(c_805, plain, (![E_234, B_235, A_236]: (E_234=B_235 | E_234=A_236 | E_234=A_236 | ~r2_hidden(E_234, k2_tarski(A_236, B_235)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_766])).
% 3.06/1.45  tff(c_882, plain, (![A_273, B_274, B_275]: ('#skF_1'(k2_tarski(A_273, B_274), B_275)=B_274 | '#skF_1'(k2_tarski(A_273, B_274), B_275)=A_273 | r1_tarski(k2_tarski(A_273, B_274), B_275))), inference(resolution, [status(thm)], [c_6, c_805])).
% 3.06/1.45  tff(c_908, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5' | '#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_882, c_729])).
% 3.06/1.45  tff(c_912, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_908])).
% 3.06/1.45  tff(c_920, plain, (~r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_912, c_4])).
% 3.06/1.45  tff(c_928, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_920])).
% 3.06/1.45  tff(c_930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_729, c_928])).
% 3.06/1.45  tff(c_931, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_908])).
% 3.06/1.45  tff(c_939, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_931, c_4])).
% 3.06/1.45  tff(c_947, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_939])).
% 3.06/1.45  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_729, c_947])).
% 3.06/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.45  
% 3.06/1.45  Inference rules
% 3.06/1.45  ----------------------
% 3.06/1.45  #Ref     : 0
% 3.06/1.45  #Sup     : 198
% 3.06/1.45  #Fact    : 0
% 3.06/1.45  #Define  : 0
% 3.06/1.45  #Split   : 8
% 3.06/1.45  #Chain   : 0
% 3.06/1.45  #Close   : 0
% 3.06/1.45  
% 3.06/1.45  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 28
% 3.06/1.46  #Demod        : 34
% 3.06/1.46  #Tautology    : 66
% 3.06/1.46  #SimpNegUnit  : 16
% 3.06/1.46  #BackRed      : 0
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.31
% 3.06/1.46  Parsing              : 0.15
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.37
% 3.06/1.46  Inferencing          : 0.14
% 3.06/1.46  Reduction            : 0.11
% 3.06/1.46  Demodulation         : 0.08
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.08
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.71
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
