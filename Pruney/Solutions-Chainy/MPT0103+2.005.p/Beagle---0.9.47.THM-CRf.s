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
% DateTime   : Thu Dec  3 09:44:46 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_26,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_1,B_2,B_32] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_32)
      | ~ r1_tarski(A_1,B_32)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_122,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,C_50)
      | ~ r2_hidden(A_49,B_51)
      | r2_hidden(A_49,k5_xboole_0(B_51,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1065,plain,(
    ! [A_203,B_204,C_205] :
      ( r1_tarski(A_203,k5_xboole_0(B_204,C_205))
      | r2_hidden('#skF_1'(A_203,k5_xboole_0(B_204,C_205)),C_205)
      | ~ r2_hidden('#skF_1'(A_203,k5_xboole_0(B_204,C_205)),B_204) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_4245,plain,(
    ! [A_471,B_472,C_473] :
      ( r2_hidden('#skF_1'(A_471,k5_xboole_0(B_472,C_473)),C_473)
      | ~ r1_tarski(A_471,B_472)
      | r1_tarski(A_471,k5_xboole_0(B_472,C_473)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1065])).

tff(c_28,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,B_35)
      | ~ r2_hidden(C_36,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,k4_xboole_0(A_39,B_38)) ) ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_72,plain,(
    ! [A_39,B_38,B_2] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_39,B_38),B_2),B_38)
      | r1_tarski(k4_xboole_0(A_39,B_38),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_4379,plain,(
    ! [A_477,C_478,B_479] :
      ( ~ r1_tarski(k4_xboole_0(A_477,C_478),B_479)
      | r1_tarski(k4_xboole_0(A_477,C_478),k5_xboole_0(B_479,C_478)) ) ),
    inference(resolution,[status(thm)],[c_4245,c_72])).

tff(c_30,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4388,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4379,c_30])).

tff(c_4395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.06  
% 5.14/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.49/2.07  
% 5.49/2.07  %Foreground sorts:
% 5.49/2.07  
% 5.49/2.07  
% 5.49/2.07  %Background operators:
% 5.49/2.07  
% 5.49/2.07  
% 5.49/2.07  %Foreground operators:
% 5.49/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.49/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.49/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.49/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.49/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.49/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.49/2.07  
% 5.49/2.08  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.49/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.49/2.08  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.49/2.08  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.49/2.08  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.49/2.08  tff(f_64, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 5.49/2.08  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.49/2.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.49/2.08  tff(c_43, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.49/2.08  tff(c_52, plain, (![A_1, B_2, B_32]: (r2_hidden('#skF_1'(A_1, B_2), B_32) | ~r1_tarski(A_1, B_32) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_43])).
% 5.49/2.08  tff(c_122, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, C_50) | ~r2_hidden(A_49, B_51) | r2_hidden(A_49, k5_xboole_0(B_51, C_50)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.49/2.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.49/2.08  tff(c_1065, plain, (![A_203, B_204, C_205]: (r1_tarski(A_203, k5_xboole_0(B_204, C_205)) | r2_hidden('#skF_1'(A_203, k5_xboole_0(B_204, C_205)), C_205) | ~r2_hidden('#skF_1'(A_203, k5_xboole_0(B_204, C_205)), B_204))), inference(resolution, [status(thm)], [c_122, c_4])).
% 5.49/2.08  tff(c_4245, plain, (![A_471, B_472, C_473]: (r2_hidden('#skF_1'(A_471, k5_xboole_0(B_472, C_473)), C_473) | ~r1_tarski(A_471, B_472) | r1_tarski(A_471, k5_xboole_0(B_472, C_473)))), inference(resolution, [status(thm)], [c_52, c_1065])).
% 5.49/2.08  tff(c_28, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.49/2.08  tff(c_53, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, B_35) | ~r2_hidden(C_36, A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.49/2.08  tff(c_57, plain, (![C_37, B_38, A_39]: (~r2_hidden(C_37, B_38) | ~r2_hidden(C_37, k4_xboole_0(A_39, B_38)))), inference(resolution, [status(thm)], [c_28, c_53])).
% 5.49/2.08  tff(c_72, plain, (![A_39, B_38, B_2]: (~r2_hidden('#skF_1'(k4_xboole_0(A_39, B_38), B_2), B_38) | r1_tarski(k4_xboole_0(A_39, B_38), B_2))), inference(resolution, [status(thm)], [c_6, c_57])).
% 5.49/2.08  tff(c_4379, plain, (![A_477, C_478, B_479]: (~r1_tarski(k4_xboole_0(A_477, C_478), B_479) | r1_tarski(k4_xboole_0(A_477, C_478), k5_xboole_0(B_479, C_478)))), inference(resolution, [status(thm)], [c_4245, c_72])).
% 5.49/2.08  tff(c_30, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.49/2.08  tff(c_4388, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_4379, c_30])).
% 5.49/2.08  tff(c_4395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_4388])).
% 5.49/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.08  
% 5.49/2.08  Inference rules
% 5.49/2.08  ----------------------
% 5.49/2.08  #Ref     : 0
% 5.49/2.08  #Sup     : 946
% 5.49/2.08  #Fact    : 6
% 5.49/2.08  #Define  : 0
% 5.49/2.08  #Split   : 0
% 5.49/2.08  #Chain   : 0
% 5.49/2.08  #Close   : 0
% 5.49/2.08  
% 5.49/2.08  Ordering : KBO
% 5.49/2.08  
% 5.49/2.08  Simplification rules
% 5.49/2.08  ----------------------
% 5.49/2.08  #Subsume      : 79
% 5.49/2.08  #Demod        : 268
% 5.49/2.08  #Tautology    : 272
% 5.49/2.08  #SimpNegUnit  : 0
% 5.49/2.08  #BackRed      : 1
% 5.49/2.08  
% 5.49/2.08  #Partial instantiations: 0
% 5.49/2.08  #Strategies tried      : 1
% 5.49/2.08  
% 5.49/2.08  Timing (in seconds)
% 5.49/2.08  ----------------------
% 5.55/2.09  Preprocessing        : 0.29
% 5.55/2.09  Parsing              : 0.17
% 5.55/2.09  CNF conversion       : 0.02
% 5.55/2.09  Main loop            : 0.95
% 5.55/2.09  Inferencing          : 0.33
% 5.55/2.09  Reduction            : 0.24
% 5.55/2.09  Demodulation         : 0.17
% 5.55/2.09  BG Simplification    : 0.04
% 5.55/2.09  Subsumption          : 0.28
% 5.55/2.09  Abstraction          : 0.05
% 5.55/2.09  MUC search           : 0.00
% 5.55/2.09  Cooper               : 0.00
% 5.55/2.09  Total                : 1.28
% 5.55/2.09  Index Insertion      : 0.00
% 5.55/2.09  Index Deletion       : 0.00
% 5.55/2.09  Index Matching       : 0.00
% 5.55/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
