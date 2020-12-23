%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    3 (   3 expanded)
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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( r1_tarski(k4_xboole_0(C_11,B_10),k4_xboole_0(C_11,A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k4_xboole_0(A_20,C_21),k4_xboole_0(B_22,C_21))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_26,C_27,B_28] :
      ( k2_xboole_0(k4_xboole_0(A_26,C_27),k4_xboole_0(B_28,C_27)) = k4_xboole_0(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_32,C_33,C_34,B_35] :
      ( r1_tarski(k4_xboole_0(A_32,C_33),C_34)
      | ~ r1_tarski(k4_xboole_0(B_35,C_33),C_34)
      | ~ r1_tarski(A_32,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_104,plain,(
    ! [A_40,B_41,C_42,A_43] :
      ( r1_tarski(k4_xboole_0(A_40,B_41),k4_xboole_0(C_42,A_43))
      | ~ r1_tarski(A_40,C_42)
      | ~ r1_tarski(A_43,B_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_10,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_4'),k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.15  
% 1.64/1.15  %Foreground sorts:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Background operators:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Foreground operators:
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.15  
% 1.64/1.16  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 1.64/1.16  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.64/1.16  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 1.64/1.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.64/1.16  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.64/1.16  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.16  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.16  tff(c_8, plain, (![C_11, B_10, A_9]: (r1_tarski(k4_xboole_0(C_11, B_10), k4_xboole_0(C_11, A_9)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.16  tff(c_46, plain, (![A_20, C_21, B_22]: (r1_tarski(k4_xboole_0(A_20, C_21), k4_xboole_0(B_22, C_21)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.16  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.16  tff(c_56, plain, (![A_26, C_27, B_28]: (k2_xboole_0(k4_xboole_0(A_26, C_27), k4_xboole_0(B_28, C_27))=k4_xboole_0(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.64/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.16  tff(c_90, plain, (![A_32, C_33, C_34, B_35]: (r1_tarski(k4_xboole_0(A_32, C_33), C_34) | ~r1_tarski(k4_xboole_0(B_35, C_33), C_34) | ~r1_tarski(A_32, B_35))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 1.64/1.16  tff(c_104, plain, (![A_40, B_41, C_42, A_43]: (r1_tarski(k4_xboole_0(A_40, B_41), k4_xboole_0(C_42, A_43)) | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_43, B_41))), inference(resolution, [status(thm)], [c_8, c_90])).
% 1.64/1.16  tff(c_10, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_4'), k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.16  tff(c_111, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_104, c_10])).
% 1.64/1.16  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_111])).
% 1.64/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  Inference rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Ref     : 0
% 1.64/1.16  #Sup     : 27
% 1.64/1.16  #Fact    : 0
% 1.64/1.16  #Define  : 0
% 1.64/1.16  #Split   : 0
% 1.64/1.16  #Chain   : 0
% 1.64/1.16  #Close   : 0
% 1.64/1.16  
% 1.64/1.16  Ordering : KBO
% 1.64/1.16  
% 1.64/1.16  Simplification rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Subsume      : 0
% 1.64/1.17  #Demod        : 2
% 1.64/1.17  #Tautology    : 10
% 1.64/1.17  #SimpNegUnit  : 0
% 1.64/1.17  #BackRed      : 0
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.17  Preprocessing        : 0.26
% 1.64/1.17  Parsing              : 0.15
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.15
% 1.64/1.17  Inferencing          : 0.07
% 1.64/1.17  Reduction            : 0.03
% 1.64/1.17  Demodulation         : 0.03
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.03
% 1.64/1.17  Abstraction          : 0.01
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.43
% 1.64/1.17  Index Insertion      : 0.00
% 1.64/1.17  Index Deletion       : 0.00
% 1.64/1.17  Index Matching       : 0.00
% 1.64/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
