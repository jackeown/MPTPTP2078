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
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  86 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_18,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_246,plain,(
    ! [A_73,C_74,B_75] :
      ( ~ r2_hidden(A_73,C_74)
      | k4_xboole_0(k2_tarski(A_73,B_75),C_74) != k1_tarski(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_250,plain,(
    ! [A_73,B_75] :
      ( ~ r2_hidden(A_73,k2_tarski(A_73,B_75))
      | k1_tarski(A_73) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_246])).

tff(c_255,plain,(
    ! [A_73] : k1_tarski(A_73) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_250])).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [B_42,C_43] :
      ( k4_xboole_0(k2_tarski(B_42,B_42),C_43) = k1_tarski(B_42)
      | r2_hidden(B_42,C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_157,plain,(
    ! [B_67,C_68] :
      ( k4_xboole_0(k1_tarski(B_67),C_68) = k1_tarski(B_67)
      | r2_hidden(B_67,C_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_97,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_90])).

tff(c_163,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_97])).

tff(c_187,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_14,plain,(
    ! [D_12,B_8,A_7] :
      ( D_12 = B_8
      | D_12 = A_7
      | ~ r2_hidden(D_12,k2_tarski(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_190,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_187,c_14])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_190])).

tff(c_195,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.28  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.08/1.28  tff(f_69, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.08/1.28  tff(f_79, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.08/1.28  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.28  tff(c_18, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.28  tff(c_90, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.28  tff(c_98, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.08/1.28  tff(c_246, plain, (![A_73, C_74, B_75]: (~r2_hidden(A_73, C_74) | k4_xboole_0(k2_tarski(A_73, B_75), C_74)!=k1_tarski(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.28  tff(c_250, plain, (![A_73, B_75]: (~r2_hidden(A_73, k2_tarski(A_73, B_75)) | k1_tarski(A_73)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_246])).
% 2.08/1.28  tff(c_255, plain, (![A_73]: (k1_tarski(A_73)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_250])).
% 2.08/1.28  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.08/1.28  tff(c_54, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.08/1.28  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.28  tff(c_50, plain, (![B_42, C_43]: (k4_xboole_0(k2_tarski(B_42, B_42), C_43)=k1_tarski(B_42) | r2_hidden(B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.28  tff(c_157, plain, (![B_67, C_68]: (k4_xboole_0(k1_tarski(B_67), C_68)=k1_tarski(B_67) | r2_hidden(B_67, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50])).
% 2.08/1.28  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.08/1.28  tff(c_97, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_90])).
% 2.08/1.28  tff(c_163, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_97])).
% 2.08/1.28  tff(c_187, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_163])).
% 2.08/1.28  tff(c_14, plain, (![D_12, B_8, A_7]: (D_12=B_8 | D_12=A_7 | ~r2_hidden(D_12, k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.28  tff(c_190, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_187, c_14])).
% 2.08/1.28  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_190])).
% 2.08/1.28  tff(c_195, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_163])).
% 2.08/1.28  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_195])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 45
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 2
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 1
% 2.08/1.28  #Demod        : 13
% 2.08/1.28  #Tautology    : 29
% 2.08/1.28  #SimpNegUnit  : 2
% 2.08/1.28  #BackRed      : 5
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.32
% 2.08/1.28  Parsing              : 0.17
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.17
% 2.08/1.28  Inferencing          : 0.06
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.02
% 2.08/1.28  Subsumption          : 0.04
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.52
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
