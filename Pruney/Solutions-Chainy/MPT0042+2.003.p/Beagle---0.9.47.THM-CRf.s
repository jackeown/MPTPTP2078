%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  63 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [C_11,B_10,A_9] :
      ( r1_tarski(k4_xboole_0(C_11,B_10),k4_xboole_0(C_11,A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k4_xboole_0(A_6,C_8),k4_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    ! [A_26,B_27,B_28] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(A_26,B_28)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_29,B_30,B_31,B_32] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(B_32,B_31)
      | ~ r1_tarski(A_29,B_32)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_31,c_2])).

tff(c_153,plain,(
    ! [A_61,A_58,B_57,B_60,C_59] :
      ( r2_hidden('#skF_1'(A_58,B_57),k4_xboole_0(B_60,C_59))
      | ~ r1_tarski(A_58,k4_xboole_0(A_61,C_59))
      | r1_tarski(A_58,B_57)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_250,plain,(
    ! [A_88,B_84,B_85,C_87,B_86] :
      ( r2_hidden('#skF_1'(k4_xboole_0(C_87,B_86),B_84),k4_xboole_0(B_85,A_88))
      | r1_tarski(k4_xboole_0(C_87,B_86),B_84)
      | ~ r1_tarski(C_87,B_85)
      | ~ r1_tarski(A_88,B_86) ) ),
    inference(resolution,[status(thm)],[c_10,c_153])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [C_89,B_90,B_91,A_92] :
      ( r1_tarski(k4_xboole_0(C_89,B_90),k4_xboole_0(B_91,A_92))
      | ~ r1_tarski(C_89,B_91)
      | ~ r1_tarski(A_92,B_90) ) ),
    inference(resolution,[status(thm)],[c_250,c_4])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_5'),k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_276,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.25  
% 2.05/1.26  tff(f_47, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 2.05/1.26  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.05/1.26  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.05/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.26  tff(c_14, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.26  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.26  tff(c_10, plain, (![C_11, B_10, A_9]: (r1_tarski(k4_xboole_0(C_11, B_10), k4_xboole_0(C_11, A_9)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.27  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(k4_xboole_0(A_6, C_8), k4_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.05/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.27  tff(c_24, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.27  tff(c_31, plain, (![A_26, B_27, B_28]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(A_26, B_28) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_6, c_24])).
% 2.05/1.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.27  tff(c_40, plain, (![A_29, B_30, B_31, B_32]: (r2_hidden('#skF_1'(A_29, B_30), B_31) | ~r1_tarski(B_32, B_31) | ~r1_tarski(A_29, B_32) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_31, c_2])).
% 2.05/1.27  tff(c_153, plain, (![A_61, A_58, B_57, B_60, C_59]: (r2_hidden('#skF_1'(A_58, B_57), k4_xboole_0(B_60, C_59)) | ~r1_tarski(A_58, k4_xboole_0(A_61, C_59)) | r1_tarski(A_58, B_57) | ~r1_tarski(A_61, B_60))), inference(resolution, [status(thm)], [c_8, c_40])).
% 2.05/1.27  tff(c_250, plain, (![A_88, B_84, B_85, C_87, B_86]: (r2_hidden('#skF_1'(k4_xboole_0(C_87, B_86), B_84), k4_xboole_0(B_85, A_88)) | r1_tarski(k4_xboole_0(C_87, B_86), B_84) | ~r1_tarski(C_87, B_85) | ~r1_tarski(A_88, B_86))), inference(resolution, [status(thm)], [c_10, c_153])).
% 2.05/1.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.27  tff(c_259, plain, (![C_89, B_90, B_91, A_92]: (r1_tarski(k4_xboole_0(C_89, B_90), k4_xboole_0(B_91, A_92)) | ~r1_tarski(C_89, B_91) | ~r1_tarski(A_92, B_90))), inference(resolution, [status(thm)], [c_250, c_4])).
% 2.05/1.27  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_5'), k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.27  tff(c_276, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_259, c_12])).
% 2.05/1.27  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_276])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 69
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 4
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 18
% 2.05/1.27  #Demod        : 3
% 2.05/1.27  #Tautology    : 2
% 2.05/1.27  #SimpNegUnit  : 0
% 2.05/1.27  #BackRed      : 0
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.25
% 2.05/1.27  Parsing              : 0.14
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.27
% 2.05/1.27  Inferencing          : 0.10
% 2.05/1.27  Reduction            : 0.06
% 2.05/1.27  Demodulation         : 0.04
% 2.05/1.27  BG Simplification    : 0.01
% 2.05/1.27  Subsumption          : 0.08
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.55
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
