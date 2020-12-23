%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  66 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_115,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,C_25)) = k4_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [C_25] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_25)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_16])).

tff(c_173,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_61])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_62,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_154,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_83])).

tff(c_174,plain,(
    ! [C_26] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_26)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_198,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',k1_xboole_0)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_202,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_34,c_198])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.16  
% 1.84/1.17  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.84/1.17  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.84/1.17  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.84/1.17  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.84/1.17  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.84/1.17  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.84/1.17  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.17  tff(c_30, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.17  tff(c_34, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_30])).
% 1.84/1.17  tff(c_115, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, C_25))=k4_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.17  tff(c_139, plain, (![C_25]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_25))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_25)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_115])).
% 1.84/1.17  tff(c_53, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.17  tff(c_16, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.17  tff(c_61, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_16])).
% 1.84/1.17  tff(c_173, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_61])).
% 1.84/1.17  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.17  tff(c_40, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.17  tff(c_48, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_40])).
% 1.84/1.17  tff(c_62, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.17  tff(c_77, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_62])).
% 1.84/1.17  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.17  tff(c_83, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 1.84/1.17  tff(c_154, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_83])).
% 1.84/1.17  tff(c_174, plain, (![C_26]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_26))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_26)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_115])).
% 1.84/1.17  tff(c_198, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', k1_xboole_0))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 1.84/1.17  tff(c_202, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_34, c_198])).
% 1.84/1.17  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_202])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 52
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 0
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 0
% 1.84/1.17  #Demod        : 11
% 1.84/1.17  #Tautology    : 25
% 1.84/1.17  #SimpNegUnit  : 1
% 1.84/1.17  #BackRed      : 1
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.17  Preprocessing        : 0.26
% 1.84/1.17  Parsing              : 0.15
% 1.84/1.17  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.17
% 1.84/1.18  Inferencing          : 0.07
% 1.84/1.18  Reduction            : 0.05
% 1.84/1.18  Demodulation         : 0.04
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.03
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.18  Cooper               : 0.00
% 1.84/1.18  Total                : 0.45
% 1.84/1.18  Index Insertion      : 0.00
% 1.84/1.18  Index Deletion       : 0.00
% 1.84/1.18  Index Matching       : 0.00
% 1.84/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
