%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:39 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  34 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = k2_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_162])).

tff(c_178,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_40,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_171,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_162])).

tff(c_177,plain,(
    k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_171])).

tff(c_188,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_177])).

tff(c_24,plain,(
    ! [D_17,A_12] : r2_hidden(D_17,k2_tarski(A_12,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_225,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_192,c_10])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:22:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.70/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.17  
% 1.93/1.17  tff(f_60, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.93/1.17  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.93/1.17  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.93/1.17  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.93/1.17  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.93/1.17  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.17  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.93/1.17  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.17  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.17  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.17  tff(c_162, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.17  tff(c_174, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=k2_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_162])).
% 1.93/1.17  tff(c_178, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_174])).
% 1.93/1.17  tff(c_40, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.17  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.17  tff(c_171, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_162])).
% 1.93/1.17  tff(c_177, plain, (k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_171])).
% 1.93/1.17  tff(c_188, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_177])).
% 1.93/1.17  tff(c_24, plain, (![D_17, A_12]: (r2_hidden(D_17, k2_tarski(A_12, D_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.17  tff(c_192, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 1.93/1.17  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.17  tff(c_225, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_192, c_10])).
% 1.93/1.17  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_225])).
% 1.93/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.17  
% 1.93/1.17  Inference rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Ref     : 0
% 1.93/1.17  #Sup     : 44
% 1.93/1.17  #Fact    : 0
% 1.93/1.17  #Define  : 0
% 1.93/1.17  #Split   : 0
% 1.93/1.17  #Chain   : 0
% 1.93/1.17  #Close   : 0
% 1.93/1.17  
% 1.93/1.17  Ordering : KBO
% 1.93/1.17  
% 1.93/1.17  Simplification rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Subsume      : 2
% 1.93/1.17  #Demod        : 10
% 1.93/1.17  #Tautology    : 36
% 1.93/1.17  #SimpNegUnit  : 1
% 1.93/1.17  #BackRed      : 0
% 1.93/1.17  
% 1.93/1.17  #Partial instantiations: 0
% 1.93/1.17  #Strategies tried      : 1
% 1.93/1.17  
% 1.93/1.17  Timing (in seconds)
% 1.93/1.17  ----------------------
% 1.93/1.18  Preprocessing        : 0.29
% 1.93/1.18  Parsing              : 0.14
% 1.93/1.18  CNF conversion       : 0.02
% 1.93/1.18  Main loop            : 0.15
% 1.93/1.18  Inferencing          : 0.05
% 1.93/1.18  Reduction            : 0.05
% 1.93/1.18  Demodulation         : 0.04
% 1.93/1.18  BG Simplification    : 0.01
% 1.93/1.18  Subsumption          : 0.03
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.46
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
