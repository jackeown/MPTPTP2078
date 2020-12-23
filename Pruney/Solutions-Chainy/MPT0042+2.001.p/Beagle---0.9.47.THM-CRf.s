%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 8.49s
% Output     : CNFRefutation 8.49s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k4_xboole_0(A_8,C_10),k4_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [C_26,B_27,A_28] :
      ( r1_tarski(k4_xboole_0(C_26,B_27),k4_xboole_0(C_26,A_28))
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_556,plain,(
    ! [C_57,B_58,A_59] :
      ( k2_xboole_0(k4_xboole_0(C_57,B_58),k4_xboole_0(C_57,A_59)) = k4_xboole_0(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,k2_xboole_0(C_19,B_20))
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_18,B_2,A_1] :
      ( r1_tarski(A_18,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_18,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_2914,plain,(
    ! [A_127,C_128,A_129,B_130] :
      ( r1_tarski(A_127,k4_xboole_0(C_128,A_129))
      | ~ r1_tarski(A_127,k4_xboole_0(C_128,B_130))
      | ~ r1_tarski(A_129,B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_101])).

tff(c_4370,plain,(
    ! [A_200,C_201,B_202,A_203] :
      ( r1_tarski(k4_xboole_0(A_200,C_201),k4_xboole_0(B_202,A_203))
      | ~ r1_tarski(A_203,C_201)
      | ~ r1_tarski(A_200,B_202) ) ),
    inference(resolution,[status(thm)],[c_8,c_2914])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_4'),k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4387,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4370,c_12])).

tff(c_4401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_4387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:36:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.49/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.49/3.08  
% 8.49/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.49/3.08  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.49/3.08  
% 8.49/3.08  %Foreground sorts:
% 8.49/3.08  
% 8.49/3.08  
% 8.49/3.08  %Background operators:
% 8.49/3.08  
% 8.49/3.08  
% 8.49/3.08  %Foreground operators:
% 8.49/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.49/3.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.49/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.49/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.49/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.49/3.08  tff('#skF_1', type, '#skF_1': $i).
% 8.49/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.49/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.49/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.49/3.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.49/3.08  
% 8.49/3.10  tff(f_50, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 8.49/3.10  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 8.49/3.10  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 8.49/3.10  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.49/3.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.49/3.10  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.49/3.10  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.49/3.10  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.49/3.10  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_tarski(k4_xboole_0(A_8, C_10), k4_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.49/3.10  tff(c_132, plain, (![C_26, B_27, A_28]: (r1_tarski(k4_xboole_0(C_26, B_27), k4_xboole_0(C_26, A_28)) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.49/3.10  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.49/3.10  tff(c_556, plain, (![C_57, B_58, A_59]: (k2_xboole_0(k4_xboole_0(C_57, B_58), k4_xboole_0(C_57, A_59))=k4_xboole_0(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(resolution, [status(thm)], [c_132, c_6])).
% 8.49/3.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.49/3.10  tff(c_86, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, k2_xboole_0(C_19, B_20)) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.49/3.10  tff(c_101, plain, (![A_18, B_2, A_1]: (r1_tarski(A_18, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_18, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 8.49/3.10  tff(c_2914, plain, (![A_127, C_128, A_129, B_130]: (r1_tarski(A_127, k4_xboole_0(C_128, A_129)) | ~r1_tarski(A_127, k4_xboole_0(C_128, B_130)) | ~r1_tarski(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_556, c_101])).
% 8.49/3.10  tff(c_4370, plain, (![A_200, C_201, B_202, A_203]: (r1_tarski(k4_xboole_0(A_200, C_201), k4_xboole_0(B_202, A_203)) | ~r1_tarski(A_203, C_201) | ~r1_tarski(A_200, B_202))), inference(resolution, [status(thm)], [c_8, c_2914])).
% 8.49/3.10  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_4'), k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.49/3.10  tff(c_4387, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4370, c_12])).
% 8.49/3.10  tff(c_4401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_4387])).
% 8.49/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.49/3.10  
% 8.49/3.10  Inference rules
% 8.49/3.10  ----------------------
% 8.49/3.10  #Ref     : 0
% 8.49/3.10  #Sup     : 1334
% 8.49/3.10  #Fact    : 0
% 8.49/3.10  #Define  : 0
% 8.49/3.10  #Split   : 5
% 8.49/3.10  #Chain   : 0
% 8.49/3.10  #Close   : 0
% 8.49/3.10  
% 8.49/3.10  Ordering : KBO
% 8.49/3.10  
% 8.49/3.10  Simplification rules
% 8.49/3.10  ----------------------
% 8.49/3.10  #Subsume      : 416
% 8.49/3.10  #Demod        : 230
% 8.49/3.10  #Tautology    : 188
% 8.49/3.10  #SimpNegUnit  : 0
% 8.49/3.10  #BackRed      : 0
% 8.49/3.10  
% 8.49/3.10  #Partial instantiations: 0
% 8.49/3.10  #Strategies tried      : 1
% 8.49/3.10  
% 8.49/3.10  Timing (in seconds)
% 8.49/3.10  ----------------------
% 8.61/3.10  Preprocessing        : 0.40
% 8.61/3.10  Parsing              : 0.22
% 8.61/3.10  CNF conversion       : 0.03
% 8.61/3.10  Main loop            : 1.82
% 8.61/3.10  Inferencing          : 0.55
% 8.61/3.10  Reduction            : 0.58
% 8.61/3.10  Demodulation         : 0.45
% 8.61/3.10  BG Simplification    : 0.08
% 8.61/3.10  Subsumption          : 0.50
% 8.61/3.10  Abstraction          : 0.09
% 8.61/3.10  MUC search           : 0.00
% 8.61/3.10  Cooper               : 0.00
% 8.61/3.10  Total                : 2.26
% 8.61/3.11  Index Insertion      : 0.00
% 8.61/3.11  Index Deletion       : 0.00
% 8.61/3.11  Index Matching       : 0.00
% 8.61/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
