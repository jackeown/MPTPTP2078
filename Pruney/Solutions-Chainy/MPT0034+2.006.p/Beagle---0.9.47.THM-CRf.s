%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_17,plain,(
    ! [B_13,A_14] : k3_xboole_0(B_13,A_14) = k3_xboole_0(A_14,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [B_13,A_14] : r1_tarski(k3_xboole_0(B_13,A_14),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_4])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_4')
      | ~ r1_tarski(A_20,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_88,plain,(
    ! [B_13] : r1_tarski(k3_xboole_0(B_13,'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_139,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,k3_xboole_0(B_28,C_29))
      | ~ r1_tarski(A_27,C_29)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_15,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_147,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_15])).

tff(c_158,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_147])).

tff(c_161,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.59/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.59/1.15  
% 1.59/1.15  %Foreground sorts:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Background operators:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Foreground operators:
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.15  
% 1.59/1.16  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.59/1.16  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 1.59/1.16  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.59/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.59/1.16  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.59/1.16  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.16  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.59/1.16  tff(c_66, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.59/1.16  tff(c_78, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_66])).
% 1.59/1.16  tff(c_17, plain, (![B_13, A_14]: (k3_xboole_0(B_13, A_14)=k3_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.16  tff(c_32, plain, (![B_13, A_14]: (r1_tarski(k3_xboole_0(B_13, A_14), A_14))), inference(superposition, [status(thm), theory('equality')], [c_17, c_4])).
% 1.59/1.16  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.59/1.16  tff(c_79, plain, (![A_20]: (r1_tarski(A_20, '#skF_4') | ~r1_tarski(A_20, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_66])).
% 1.59/1.16  tff(c_88, plain, (![B_13]: (r1_tarski(k3_xboole_0(B_13, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_79])).
% 1.59/1.16  tff(c_139, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, k3_xboole_0(B_28, C_29)) | ~r1_tarski(A_27, C_29) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.16  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.59/1.16  tff(c_15, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.59/1.16  tff(c_147, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_139, c_15])).
% 1.59/1.16  tff(c_158, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_147])).
% 1.59/1.16  tff(c_161, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_78, c_158])).
% 1.59/1.16  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_161])).
% 1.59/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  Inference rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Ref     : 0
% 1.59/1.16  #Sup     : 35
% 1.59/1.16  #Fact    : 0
% 1.59/1.16  #Define  : 0
% 1.59/1.16  #Split   : 0
% 1.59/1.16  #Chain   : 0
% 1.59/1.16  #Close   : 0
% 1.59/1.16  
% 1.59/1.16  Ordering : KBO
% 1.59/1.16  
% 1.59/1.16  Simplification rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Subsume      : 2
% 1.59/1.16  #Demod        : 10
% 1.59/1.16  #Tautology    : 16
% 1.59/1.16  #SimpNegUnit  : 0
% 1.59/1.16  #BackRed      : 0
% 1.59/1.16  
% 1.59/1.16  #Partial instantiations: 0
% 1.59/1.16  #Strategies tried      : 1
% 1.59/1.16  
% 1.59/1.16  Timing (in seconds)
% 1.59/1.16  ----------------------
% 1.59/1.16  Preprocessing        : 0.25
% 1.59/1.16  Parsing              : 0.14
% 1.59/1.16  CNF conversion       : 0.01
% 1.59/1.16  Main loop            : 0.15
% 1.59/1.16  Inferencing          : 0.05
% 1.59/1.16  Reduction            : 0.06
% 1.59/1.16  Demodulation         : 0.05
% 1.59/1.16  BG Simplification    : 0.01
% 1.59/1.16  Subsumption          : 0.03
% 1.59/1.16  Abstraction          : 0.01
% 1.59/1.16  MUC search           : 0.00
% 1.59/1.16  Cooper               : 0.00
% 1.59/1.16  Total                : 0.42
% 1.59/1.16  Index Insertion      : 0.00
% 1.59/1.16  Index Deletion       : 0.00
% 1.59/1.16  Index Matching       : 0.00
% 1.59/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
