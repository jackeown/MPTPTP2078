%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),k1_tarski(B_25))
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [B_23] : ~ r1_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,k3_xboole_0(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8])).

tff(c_127,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_154,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_183,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_12,plain,(
    ! [C_15,A_13,B_14] :
      ( r1_xboole_0(k3_xboole_0(C_15,A_13),k3_xboole_0(C_15,B_14))
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_244,plain,(
    ! [A_57,A_58] :
      ( r1_xboole_0(k3_xboole_0(A_57,A_58),A_57)
      | ~ r1_xboole_0(A_58,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12])).

tff(c_253,plain,
    ( r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
    | ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_244])).

tff(c_257,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_253])).

tff(c_260,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_257])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  %$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.02/1.25  
% 2.02/1.25  %Foreground sorts:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Background operators:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Foreground operators:
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.25  
% 2.02/1.26  tff(f_62, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.02/1.26  tff(f_57, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.02/1.26  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.02/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.02/1.26  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.26  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.02/1.26  tff(f_39, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.02/1.26  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.26  tff(c_22, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), k1_tarski(B_25)) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.26  tff(c_20, plain, (![B_23]: (~r1_xboole_0(k1_tarski(B_23), k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.26  tff(c_26, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.26  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.26  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.26  tff(c_88, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.26  tff(c_97, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, k3_xboole_0(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8])).
% 2.02/1.26  tff(c_127, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 2.02/1.26  tff(c_154, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 2.02/1.26  tff(c_183, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_154])).
% 2.02/1.26  tff(c_12, plain, (![C_15, A_13, B_14]: (r1_xboole_0(k3_xboole_0(C_15, A_13), k3_xboole_0(C_15, B_14)) | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.26  tff(c_244, plain, (![A_57, A_58]: (r1_xboole_0(k3_xboole_0(A_57, A_58), A_57) | ~r1_xboole_0(A_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_183, c_12])).
% 2.02/1.26  tff(c_253, plain, (r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | ~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_244])).
% 2.02/1.26  tff(c_257, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_20, c_253])).
% 2.02/1.26  tff(c_260, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_22, c_257])).
% 2.02/1.26  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_260])).
% 2.02/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  Inference rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Ref     : 0
% 2.02/1.26  #Sup     : 60
% 2.02/1.26  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 0
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 0
% 2.02/1.26  #Demod        : 28
% 2.02/1.26  #Tautology    : 33
% 2.02/1.26  #SimpNegUnit  : 2
% 2.02/1.26  #BackRed      : 2
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.27  Preprocessing        : 0.29
% 2.02/1.27  Parsing              : 0.16
% 2.02/1.27  CNF conversion       : 0.02
% 2.02/1.27  Main loop            : 0.17
% 2.02/1.27  Inferencing          : 0.06
% 2.02/1.27  Reduction            : 0.06
% 2.02/1.27  Demodulation         : 0.05
% 2.02/1.27  BG Simplification    : 0.01
% 2.02/1.27  Subsumption          : 0.02
% 2.02/1.27  Abstraction          : 0.01
% 2.02/1.27  MUC search           : 0.00
% 2.02/1.27  Cooper               : 0.00
% 2.02/1.27  Total                : 0.48
% 2.02/1.27  Index Insertion      : 0.00
% 2.02/1.27  Index Deletion       : 0.00
% 2.02/1.27  Index Matching       : 0.00
% 2.02/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
