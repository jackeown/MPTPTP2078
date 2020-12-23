%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  53 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_25,B_26,C_27] : k3_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k3_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_304,plain,(
    ! [A_48,B_49,C_50,C_51] :
      ( ~ r1_xboole_0(k3_xboole_0(A_48,B_49),C_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_48,k3_xboole_0(B_49,C_50))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_327,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(k3_xboole_0(A_52,B_53),C_54)
      | r1_xboole_0(A_52,k3_xboole_0(B_53,C_54)) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_341,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_327])).

tff(c_12,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k4_xboole_0(A_32,B_33),k4_xboole_0(A_32,C_34)) = k4_xboole_0(A_32,k3_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_35,C_36] : k4_xboole_0(A_35,k3_xboole_0(C_36,C_36)) = k4_xboole_0(A_35,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_2])).

tff(c_135,plain,(
    ! [A_35,C_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,C_36)) = k3_xboole_0(A_35,k3_xboole_0(C_36,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_12])).

tff(c_188,plain,(
    ! [A_38,C_39] : k3_xboole_0(A_38,k3_xboole_0(C_39,C_39)) = k3_xboole_0(A_38,C_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_135])).

tff(c_215,plain,(
    ! [A_38,C_39,C_7] :
      ( ~ r1_xboole_0(A_38,k3_xboole_0(C_39,C_39))
      | ~ r2_hidden(C_7,k3_xboole_0(A_38,C_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6])).

tff(c_345,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_341,c_215])).

tff(c_349,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_345])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.17/1.35  
% 2.17/1.35  %Foreground sorts:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Background operators:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Foreground operators:
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.35  
% 2.17/1.36  tff(f_56, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.17/1.36  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.36  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.17/1.36  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.17/1.36  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 2.17/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.17/1.36  tff(c_18, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.36  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.36  tff(c_16, plain, (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.36  tff(c_44, plain, (![A_25, B_26, C_27]: (k3_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k3_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.36  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.36  tff(c_304, plain, (![A_48, B_49, C_50, C_51]: (~r1_xboole_0(k3_xboole_0(A_48, B_49), C_50) | ~r2_hidden(C_51, k3_xboole_0(A_48, k3_xboole_0(B_49, C_50))))), inference(superposition, [status(thm), theory('equality')], [c_44, c_6])).
% 2.17/1.36  tff(c_327, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(k3_xboole_0(A_52, B_53), C_54) | r1_xboole_0(A_52, k3_xboole_0(B_53, C_54)))), inference(resolution, [status(thm)], [c_4, c_304])).
% 2.17/1.36  tff(c_341, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_327])).
% 2.17/1.36  tff(c_12, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.36  tff(c_89, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k4_xboole_0(A_32, C_34))=k4_xboole_0(A_32, k3_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.36  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.36  tff(c_119, plain, (![A_35, C_36]: (k4_xboole_0(A_35, k3_xboole_0(C_36, C_36))=k4_xboole_0(A_35, C_36))), inference(superposition, [status(thm), theory('equality')], [c_89, c_2])).
% 2.17/1.36  tff(c_135, plain, (![A_35, C_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, C_36))=k3_xboole_0(A_35, k3_xboole_0(C_36, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_12])).
% 2.17/1.36  tff(c_188, plain, (![A_38, C_39]: (k3_xboole_0(A_38, k3_xboole_0(C_39, C_39))=k3_xboole_0(A_38, C_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_135])).
% 2.17/1.36  tff(c_215, plain, (![A_38, C_39, C_7]: (~r1_xboole_0(A_38, k3_xboole_0(C_39, C_39)) | ~r2_hidden(C_7, k3_xboole_0(A_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_6])).
% 2.17/1.36  tff(c_345, plain, (![C_55]: (~r2_hidden(C_55, k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_341, c_215])).
% 2.17/1.36  tff(c_349, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_345])).
% 2.17/1.36  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_349])).
% 2.17/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.36  
% 2.17/1.36  Inference rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Ref     : 0
% 2.17/1.36  #Sup     : 81
% 2.17/1.36  #Fact    : 0
% 2.17/1.36  #Define  : 0
% 2.17/1.36  #Split   : 0
% 2.17/1.36  #Chain   : 0
% 2.17/1.36  #Close   : 0
% 2.17/1.36  
% 2.17/1.36  Ordering : KBO
% 2.17/1.36  
% 2.17/1.36  Simplification rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Subsume      : 1
% 2.17/1.36  #Demod        : 54
% 2.17/1.36  #Tautology    : 37
% 2.17/1.36  #SimpNegUnit  : 1
% 2.17/1.36  #BackRed      : 0
% 2.17/1.36  
% 2.17/1.36  #Partial instantiations: 0
% 2.17/1.36  #Strategies tried      : 1
% 2.17/1.36  
% 2.17/1.36  Timing (in seconds)
% 2.17/1.36  ----------------------
% 2.17/1.36  Preprocessing        : 0.31
% 2.17/1.36  Parsing              : 0.16
% 2.17/1.36  CNF conversion       : 0.02
% 2.17/1.36  Main loop            : 0.23
% 2.17/1.36  Inferencing          : 0.10
% 2.17/1.36  Reduction            : 0.07
% 2.17/1.36  Demodulation         : 0.06
% 2.17/1.36  BG Simplification    : 0.01
% 2.17/1.36  Subsumption          : 0.03
% 2.17/1.36  Abstraction          : 0.01
% 2.17/1.36  MUC search           : 0.00
% 2.17/1.36  Cooper               : 0.00
% 2.17/1.36  Total                : 0.57
% 2.17/1.36  Index Insertion      : 0.00
% 2.17/1.36  Index Deletion       : 0.00
% 2.17/1.36  Index Matching       : 0.00
% 2.17/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
