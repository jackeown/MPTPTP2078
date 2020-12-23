%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  86 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_20,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_372,plain,(
    ! [A_59,C_60,B_61] :
      ( ~ r2_hidden(A_59,C_60)
      | k4_xboole_0(k2_tarski(A_59,B_61),C_60) != k1_tarski(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_376,plain,(
    ! [A_59,B_61] :
      ( ~ r2_hidden(A_59,k2_tarski(A_59,B_61))
      | k1_tarski(A_59) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_372])).

tff(c_381,plain,(
    ! [A_59] : k1_tarski(A_59) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_376])).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [B_19,C_20] :
      ( k4_xboole_0(k2_tarski(B_19,B_19),C_20) = k1_tarski(B_19)
      | r2_hidden(B_19,C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_181,plain,(
    ! [B_45,C_46] :
      ( k4_xboole_0(k1_tarski(B_45),C_46) = k1_tarski(B_45)
      | r2_hidden(B_45,C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_50,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_190,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_107])).

tff(c_209,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_211,plain,(
    ! [D_47,B_48,A_49] :
      ( D_47 = B_48
      | D_47 = A_49
      | ~ r2_hidden(D_47,k2_tarski(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_214,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_211])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_214])).

tff(c_228,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  %$ r2_hidden > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.27  
% 2.15/1.28  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.15/1.28  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.28  tff(f_63, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.15/1.28  tff(f_73, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.15/1.28  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.28  tff(c_20, plain, (![D_14, B_10]: (r2_hidden(D_14, k2_tarski(D_14, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.28  tff(c_96, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.28  tff(c_108, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.15/1.28  tff(c_372, plain, (![A_59, C_60, B_61]: (~r2_hidden(A_59, C_60) | k4_xboole_0(k2_tarski(A_59, B_61), C_60)!=k1_tarski(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.28  tff(c_376, plain, (![A_59, B_61]: (~r2_hidden(A_59, k2_tarski(A_59, B_61)) | k1_tarski(A_59)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_372])).
% 2.15/1.28  tff(c_381, plain, (![A_59]: (k1_tarski(A_59)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_376])).
% 2.15/1.28  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.28  tff(c_46, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.28  tff(c_34, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.28  tff(c_42, plain, (![B_19, C_20]: (k4_xboole_0(k2_tarski(B_19, B_19), C_20)=k1_tarski(B_19) | r2_hidden(B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.28  tff(c_181, plain, (![B_45, C_46]: (k4_xboole_0(k1_tarski(B_45), C_46)=k1_tarski(B_45) | r2_hidden(B_45, C_46))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.15/1.28  tff(c_50, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.28  tff(c_107, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_96])).
% 2.15/1.28  tff(c_190, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_107])).
% 2.15/1.28  tff(c_209, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_190])).
% 2.15/1.28  tff(c_211, plain, (![D_47, B_48, A_49]: (D_47=B_48 | D_47=A_49 | ~r2_hidden(D_47, k2_tarski(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.28  tff(c_214, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_209, c_211])).
% 2.15/1.28  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_214])).
% 2.15/1.28  tff(c_228, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_190])).
% 2.15/1.28  tff(c_383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_228])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 76
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 2
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.28  
% 2.15/1.28  Ordering : KBO
% 2.15/1.28  
% 2.15/1.28  Simplification rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Subsume      : 1
% 2.15/1.28  #Demod        : 31
% 2.15/1.28  #Tautology    : 51
% 2.15/1.28  #SimpNegUnit  : 3
% 2.15/1.28  #BackRed      : 4
% 2.15/1.28  
% 2.15/1.28  #Partial instantiations: 0
% 2.15/1.28  #Strategies tried      : 1
% 2.15/1.28  
% 2.15/1.28  Timing (in seconds)
% 2.15/1.28  ----------------------
% 2.15/1.28  Preprocessing        : 0.31
% 2.15/1.28  Parsing              : 0.16
% 2.15/1.28  CNF conversion       : 0.02
% 2.15/1.28  Main loop            : 0.21
% 2.15/1.28  Inferencing          : 0.07
% 2.15/1.28  Reduction            : 0.07
% 2.15/1.28  Demodulation         : 0.05
% 2.15/1.28  BG Simplification    : 0.02
% 2.15/1.28  Subsumption          : 0.04
% 2.15/1.28  Abstraction          : 0.01
% 2.15/1.28  MUC search           : 0.00
% 2.15/1.28  Cooper               : 0.00
% 2.15/1.28  Total                : 0.55
% 2.15/1.28  Index Insertion      : 0.00
% 2.15/1.28  Index Deletion       : 0.00
% 2.15/1.28  Index Matching       : 0.00
% 2.15/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
