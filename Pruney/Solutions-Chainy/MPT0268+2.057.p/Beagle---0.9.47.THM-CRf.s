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
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 164 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_48,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_218,plain,(
    ! [E_81,C_82,B_83,A_84] :
      ( E_81 = C_82
      | E_81 = B_83
      | E_81 = A_84
      | ~ r2_hidden(E_81,k1_enumset1(A_84,B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_364,plain,(
    ! [E_128,B_129,A_130] :
      ( E_128 = B_129
      | E_128 = A_130
      | E_128 = A_130
      | ~ r2_hidden(E_128,k2_tarski(A_130,B_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_218])).

tff(c_388,plain,(
    ! [E_131,A_132] :
      ( E_131 = A_132
      | E_131 = A_132
      | E_131 = A_132
      | ~ r2_hidden(E_131,k1_tarski(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_364])).

tff(c_404,plain,(
    ! [A_133,A_134] :
      ( '#skF_1'(A_133,k1_tarski(A_134)) = A_134
      | r1_xboole_0(A_133,k1_tarski(A_134)) ) ),
    inference(resolution,[status(thm)],[c_4,c_388])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_422,plain,(
    ! [A_141,A_142] :
      ( k4_xboole_0(A_141,k1_tarski(A_142)) = A_141
      | '#skF_1'(A_141,k1_tarski(A_142)) = A_142 ) ),
    inference(resolution,[status(thm)],[c_404,c_10])).

tff(c_446,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_109])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_455,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_6])).

tff(c_459,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_455])).

tff(c_465,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_459,c_10])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_465])).

tff(c_471,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_472,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_513,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_52])).

tff(c_79,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_47,B_48] : r2_hidden(A_47,k2_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_100,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_97])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_496,plain,(
    ! [A_150,B_151,C_152] :
      ( ~ r1_xboole_0(A_150,B_151)
      | ~ r2_hidden(C_152,B_151)
      | ~ r2_hidden(C_152,A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_592,plain,(
    ! [C_167,B_168,A_169] :
      ( ~ r2_hidden(C_167,B_168)
      | ~ r2_hidden(C_167,A_169)
      | k4_xboole_0(A_169,B_168) != A_169 ) ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_669,plain,(
    ! [A_175,A_176] :
      ( ~ r2_hidden(A_175,A_176)
      | k4_xboole_0(A_176,k1_tarski(A_175)) != A_176 ) ),
    inference(resolution,[status(thm)],[c_100,c_592])).

tff(c_672,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_669])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_672])).

tff(c_684,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_685,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_714,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_54])).

tff(c_690,plain,(
    ! [A_186,B_187] : k1_enumset1(A_186,A_186,B_187) = k2_tarski(A_186,B_187) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_708,plain,(
    ! [B_188,A_189] : r2_hidden(B_188,k2_tarski(A_189,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_16])).

tff(c_711,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_708])).

tff(c_747,plain,(
    ! [A_205,B_206,C_207] :
      ( ~ r1_xboole_0(A_205,B_206)
      | ~ r2_hidden(C_207,B_206)
      | ~ r2_hidden(C_207,A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_773,plain,(
    ! [C_213,B_214,A_215] :
      ( ~ r2_hidden(C_213,B_214)
      | ~ r2_hidden(C_213,A_215)
      | k4_xboole_0(A_215,B_214) != A_215 ) ),
    inference(resolution,[status(thm)],[c_12,c_747])).

tff(c_911,plain,(
    ! [A_225,A_226] :
      ( ~ r2_hidden(A_225,A_226)
      | k4_xboole_0(A_226,k1_tarski(A_225)) != A_226 ) ),
    inference(resolution,[status(thm)],[c_711,c_773])).

tff(c_918,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_911])).

tff(c_923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.31  
% 2.70/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.31  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.70/1.31  
% 2.70/1.31  %Foreground sorts:
% 2.70/1.31  
% 2.70/1.31  
% 2.70/1.31  %Background operators:
% 2.70/1.31  
% 2.70/1.31  
% 2.70/1.31  %Foreground operators:
% 2.70/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.70/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.70/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.31  
% 2.70/1.33  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.70/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.70/1.33  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.33  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.70/1.33  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.70/1.33  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.70/1.33  tff(c_48, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.33  tff(c_109, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.70/1.33  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.33  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.70/1.33  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.33  tff(c_38, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.33  tff(c_40, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.33  tff(c_218, plain, (![E_81, C_82, B_83, A_84]: (E_81=C_82 | E_81=B_83 | E_81=A_84 | ~r2_hidden(E_81, k1_enumset1(A_84, B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.33  tff(c_364, plain, (![E_128, B_129, A_130]: (E_128=B_129 | E_128=A_130 | E_128=A_130 | ~r2_hidden(E_128, k2_tarski(A_130, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_218])).
% 2.70/1.33  tff(c_388, plain, (![E_131, A_132]: (E_131=A_132 | E_131=A_132 | E_131=A_132 | ~r2_hidden(E_131, k1_tarski(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_364])).
% 2.70/1.33  tff(c_404, plain, (![A_133, A_134]: ('#skF_1'(A_133, k1_tarski(A_134))=A_134 | r1_xboole_0(A_133, k1_tarski(A_134)))), inference(resolution, [status(thm)], [c_4, c_388])).
% 2.70/1.33  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.33  tff(c_422, plain, (![A_141, A_142]: (k4_xboole_0(A_141, k1_tarski(A_142))=A_141 | '#skF_1'(A_141, k1_tarski(A_142))=A_142)), inference(resolution, [status(thm)], [c_404, c_10])).
% 2.70/1.33  tff(c_446, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_422, c_109])).
% 2.70/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.33  tff(c_455, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_446, c_6])).
% 2.70/1.33  tff(c_459, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_455])).
% 2.70/1.33  tff(c_465, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_459, c_10])).
% 2.70/1.33  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_465])).
% 2.70/1.33  tff(c_471, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 2.70/1.33  tff(c_472, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.70/1.33  tff(c_52, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.33  tff(c_513, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_472, c_52])).
% 2.70/1.33  tff(c_79, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.33  tff(c_20, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.33  tff(c_97, plain, (![A_47, B_48]: (r2_hidden(A_47, k2_tarski(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 2.70/1.33  tff(c_100, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_97])).
% 2.70/1.33  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.33  tff(c_496, plain, (![A_150, B_151, C_152]: (~r1_xboole_0(A_150, B_151) | ~r2_hidden(C_152, B_151) | ~r2_hidden(C_152, A_150))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.33  tff(c_592, plain, (![C_167, B_168, A_169]: (~r2_hidden(C_167, B_168) | ~r2_hidden(C_167, A_169) | k4_xboole_0(A_169, B_168)!=A_169)), inference(resolution, [status(thm)], [c_12, c_496])).
% 2.70/1.33  tff(c_669, plain, (![A_175, A_176]: (~r2_hidden(A_175, A_176) | k4_xboole_0(A_176, k1_tarski(A_175))!=A_176)), inference(resolution, [status(thm)], [c_100, c_592])).
% 2.70/1.33  tff(c_672, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_513, c_669])).
% 2.70/1.33  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_471, c_672])).
% 2.70/1.33  tff(c_684, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 2.70/1.33  tff(c_685, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.70/1.33  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.33  tff(c_714, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_685, c_54])).
% 2.70/1.33  tff(c_690, plain, (![A_186, B_187]: (k1_enumset1(A_186, A_186, B_187)=k2_tarski(A_186, B_187))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.33  tff(c_16, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.33  tff(c_708, plain, (![B_188, A_189]: (r2_hidden(B_188, k2_tarski(A_189, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_690, c_16])).
% 2.70/1.33  tff(c_711, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_708])).
% 2.70/1.33  tff(c_747, plain, (![A_205, B_206, C_207]: (~r1_xboole_0(A_205, B_206) | ~r2_hidden(C_207, B_206) | ~r2_hidden(C_207, A_205))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.33  tff(c_773, plain, (![C_213, B_214, A_215]: (~r2_hidden(C_213, B_214) | ~r2_hidden(C_213, A_215) | k4_xboole_0(A_215, B_214)!=A_215)), inference(resolution, [status(thm)], [c_12, c_747])).
% 2.70/1.33  tff(c_911, plain, (![A_225, A_226]: (~r2_hidden(A_225, A_226) | k4_xboole_0(A_226, k1_tarski(A_225))!=A_226)), inference(resolution, [status(thm)], [c_711, c_773])).
% 2.70/1.33  tff(c_918, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_714, c_911])).
% 2.70/1.33  tff(c_923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_684, c_918])).
% 2.70/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.33  
% 2.70/1.33  Inference rules
% 2.70/1.33  ----------------------
% 2.70/1.33  #Ref     : 0
% 2.70/1.33  #Sup     : 201
% 2.70/1.33  #Fact    : 0
% 2.70/1.33  #Define  : 0
% 2.70/1.33  #Split   : 3
% 2.70/1.33  #Chain   : 0
% 2.70/1.33  #Close   : 0
% 2.70/1.33  
% 2.70/1.33  Ordering : KBO
% 2.70/1.33  
% 2.70/1.33  Simplification rules
% 2.70/1.33  ----------------------
% 2.70/1.33  #Subsume      : 17
% 2.70/1.33  #Demod        : 26
% 2.70/1.33  #Tautology    : 68
% 2.70/1.33  #SimpNegUnit  : 2
% 2.70/1.33  #BackRed      : 0
% 2.70/1.33  
% 2.70/1.33  #Partial instantiations: 0
% 2.70/1.33  #Strategies tried      : 1
% 2.70/1.33  
% 2.70/1.33  Timing (in seconds)
% 2.70/1.33  ----------------------
% 2.98/1.33  Preprocessing        : 0.32
% 2.98/1.33  Parsing              : 0.16
% 2.98/1.33  CNF conversion       : 0.02
% 2.98/1.33  Main loop            : 0.35
% 2.98/1.33  Inferencing          : 0.14
% 2.98/1.33  Reduction            : 0.09
% 2.98/1.33  Demodulation         : 0.07
% 2.98/1.33  BG Simplification    : 0.02
% 2.98/1.33  Subsumption          : 0.06
% 2.98/1.33  Abstraction          : 0.02
% 2.98/1.33  MUC search           : 0.00
% 2.98/1.33  Cooper               : 0.00
% 2.98/1.33  Total                : 0.70
% 2.98/1.33  Index Insertion      : 0.00
% 2.98/1.33  Index Deletion       : 0.00
% 2.98/1.33  Index Matching       : 0.00
% 2.98/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
