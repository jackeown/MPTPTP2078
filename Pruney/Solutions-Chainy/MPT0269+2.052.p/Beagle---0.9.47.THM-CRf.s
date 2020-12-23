%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,k1_tarski(B_23)) = A_22
      | r2_hidden(B_23,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_26])).

tff(c_79,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_71])).

tff(c_246,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(B_39,k1_tarski(A_40)) = k1_tarski(A_40)
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_134,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_130])).

tff(c_93,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_135,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_111])).

tff(c_252,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_135])).

tff(c_272,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_252])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.16  
% 1.93/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.16  
% 1.93/1.16  %Foreground sorts:
% 1.93/1.16  
% 1.93/1.16  
% 1.93/1.16  %Background operators:
% 1.93/1.16  
% 1.93/1.16  
% 1.93/1.16  %Foreground operators:
% 1.93/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.16  
% 1.93/1.17  tff(f_58, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.93/1.17  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.93/1.17  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.93/1.17  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.93/1.17  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.93/1.17  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.93/1.17  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.93/1.17  tff(c_22, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.17  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.17  tff(c_65, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k1_tarski(B_23))=A_22 | r2_hidden(B_23, A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.17  tff(c_26, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.17  tff(c_71, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_26])).
% 1.93/1.17  tff(c_79, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_71])).
% 1.93/1.17  tff(c_246, plain, (![B_39, A_40]: (k3_xboole_0(B_39, k1_tarski(A_40))=k1_tarski(A_40) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.17  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.17  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.17  tff(c_118, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.17  tff(c_130, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_118])).
% 1.93/1.17  tff(c_134, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_130])).
% 1.93/1.17  tff(c_93, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.17  tff(c_111, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_93])).
% 1.93/1.17  tff(c_135, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_111])).
% 1.93/1.17  tff(c_252, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_135])).
% 1.93/1.17  tff(c_272, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_252])).
% 1.93/1.17  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_272])).
% 1.93/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.17  
% 1.93/1.17  Inference rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Ref     : 0
% 1.93/1.17  #Sup     : 61
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
% 1.93/1.17  #Demod        : 13
% 1.93/1.17  #Tautology    : 42
% 1.93/1.17  #SimpNegUnit  : 3
% 1.93/1.17  #BackRed      : 1
% 1.93/1.17  
% 1.93/1.17  #Partial instantiations: 0
% 1.93/1.17  #Strategies tried      : 1
% 1.93/1.17  
% 1.93/1.17  Timing (in seconds)
% 1.93/1.17  ----------------------
% 1.93/1.18  Preprocessing        : 0.29
% 1.93/1.18  Parsing              : 0.16
% 1.93/1.18  CNF conversion       : 0.02
% 1.93/1.18  Main loop            : 0.15
% 1.93/1.18  Inferencing          : 0.07
% 1.93/1.18  Reduction            : 0.05
% 1.93/1.18  Demodulation         : 0.03
% 1.93/1.18  BG Simplification    : 0.01
% 1.93/1.18  Subsumption          : 0.02
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.46
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
