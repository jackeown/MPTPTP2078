%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  24 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_62])).

tff(c_102,plain,(
    ! [A_18,B_19,C_20] : k3_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k3_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_12,A_13] : k3_xboole_0(B_12,A_13) = k3_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [B_12,A_13] : r1_tarski(k3_xboole_0(B_12,A_13),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6])).

tff(c_152,plain,(
    ! [A_21,B_22,C_23] : r1_tarski(k3_xboole_0(A_21,k3_xboole_0(B_22,C_23)),C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_29])).

tff(c_187,plain,(
    ! [A_24] : r1_tarski(k3_xboole_0(A_24,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_152])).

tff(c_200,plain,(
    ! [A_1] : r1_tarski(k3_xboole_0('#skF_1',A_1),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_187])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:05:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.16  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.16  
% 1.67/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.67/1.17  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.67/1.17  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.67/1.17  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.67/1.17  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.67/1.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.17  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.17  tff(c_62, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.17  tff(c_74, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_62])).
% 1.67/1.17  tff(c_102, plain, (![A_18, B_19, C_20]: (k3_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.17  tff(c_14, plain, (![B_12, A_13]: (k3_xboole_0(B_12, A_13)=k3_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.17  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.17  tff(c_29, plain, (![B_12, A_13]: (r1_tarski(k3_xboole_0(B_12, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6])).
% 1.67/1.17  tff(c_152, plain, (![A_21, B_22, C_23]: (r1_tarski(k3_xboole_0(A_21, k3_xboole_0(B_22, C_23)), C_23))), inference(superposition, [status(thm), theory('equality')], [c_102, c_29])).
% 1.67/1.17  tff(c_187, plain, (![A_24]: (r1_tarski(k3_xboole_0(A_24, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_152])).
% 1.67/1.17  tff(c_200, plain, (![A_1]: (r1_tarski(k3_xboole_0('#skF_1', A_1), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_187])).
% 1.67/1.17  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.17  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_10])).
% 1.67/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  Inference rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Ref     : 0
% 1.67/1.17  #Sup     : 52
% 1.67/1.17  #Fact    : 0
% 1.67/1.17  #Define  : 0
% 1.67/1.17  #Split   : 0
% 1.67/1.17  #Chain   : 0
% 1.67/1.17  #Close   : 0
% 1.67/1.17  
% 1.67/1.17  Ordering : KBO
% 1.67/1.17  
% 1.67/1.17  Simplification rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Subsume      : 0
% 1.67/1.17  #Demod        : 17
% 1.67/1.17  #Tautology    : 24
% 1.67/1.17  #SimpNegUnit  : 0
% 1.67/1.17  #BackRed      : 1
% 1.67/1.17  
% 1.67/1.17  #Partial instantiations: 0
% 1.67/1.17  #Strategies tried      : 1
% 1.67/1.17  
% 1.67/1.17  Timing (in seconds)
% 1.67/1.17  ----------------------
% 1.67/1.18  Preprocessing        : 0.25
% 1.67/1.18  Parsing              : 0.14
% 1.67/1.18  CNF conversion       : 0.01
% 1.86/1.18  Main loop            : 0.17
% 1.86/1.18  Inferencing          : 0.06
% 1.86/1.18  Reduction            : 0.07
% 1.86/1.18  Demodulation         : 0.06
% 1.86/1.18  BG Simplification    : 0.01
% 1.86/1.18  Subsumption          : 0.03
% 1.86/1.18  Abstraction          : 0.01
% 1.86/1.18  MUC search           : 0.00
% 1.86/1.18  Cooper               : 0.00
% 1.86/1.18  Total                : 0.44
% 1.86/1.18  Index Insertion      : 0.00
% 1.86/1.18  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
