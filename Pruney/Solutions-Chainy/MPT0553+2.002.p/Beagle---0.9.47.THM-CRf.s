%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  40 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_213,plain,(
    ! [C_48,A_49,B_50] :
      ( k2_xboole_0(k9_relat_1(C_48,A_49),k9_relat_1(C_48,B_50)) = k9_relat_1(C_48,k2_xboole_0(A_49,B_50))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_275,plain,(
    ! [C_51,A_52,B_53] :
      ( r1_tarski(k9_relat_1(C_51,A_52),k9_relat_1(C_51,k2_xboole_0(A_52,B_53)))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(k4_xboole_0(A_35,B_36),C_37)
      | ~ r1_tarski(A_35,k2_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_153,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_xboole_0(k9_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_149,c_17])).

tff(c_228,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_153])).

tff(c_273,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_4,c_228])).

tff(c_278,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_273])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.32  
% 2.01/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.32  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.01/1.32  
% 2.01/1.32  %Foreground sorts:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Background operators:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Foreground operators:
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.01/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.01/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.32  
% 2.30/1.33  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 2.30/1.33  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 2.30/1.33  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.30/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.30/1.33  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.30/1.33  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.30/1.33  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.30/1.33  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.33  tff(c_213, plain, (![C_48, A_49, B_50]: (k2_xboole_0(k9_relat_1(C_48, A_49), k9_relat_1(C_48, B_50))=k9_relat_1(C_48, k2_xboole_0(A_49, B_50)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.33  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.33  tff(c_275, plain, (![C_51, A_52, B_53]: (r1_tarski(k9_relat_1(C_51, A_52), k9_relat_1(C_51, k2_xboole_0(A_52, B_53))) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8])).
% 2.30/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.33  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.33  tff(c_149, plain, (![A_35, B_36, C_37]: (r1_tarski(k4_xboole_0(A_35, B_36), C_37) | ~r1_tarski(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.33  tff(c_10, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.33  tff(c_14, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.33  tff(c_17, plain, (~r1_tarski(k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 2.30/1.33  tff(c_153, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k9_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_149, c_17])).
% 2.30/1.33  tff(c_228, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_213, c_153])).
% 2.30/1.33  tff(c_273, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_4, c_228])).
% 2.30/1.33  tff(c_278, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_275, c_273])).
% 2.30/1.33  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_278])).
% 2.30/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  Inference rules
% 2.30/1.33  ----------------------
% 2.30/1.33  #Ref     : 0
% 2.30/1.33  #Sup     : 73
% 2.30/1.33  #Fact    : 0
% 2.30/1.33  #Define  : 0
% 2.30/1.33  #Split   : 0
% 2.30/1.33  #Chain   : 0
% 2.30/1.33  #Close   : 0
% 2.30/1.33  
% 2.30/1.33  Ordering : KBO
% 2.30/1.33  
% 2.30/1.33  Simplification rules
% 2.30/1.33  ----------------------
% 2.30/1.33  #Subsume      : 0
% 2.30/1.33  #Demod        : 25
% 2.30/1.33  #Tautology    : 33
% 2.30/1.33  #SimpNegUnit  : 0
% 2.30/1.33  #BackRed      : 0
% 2.30/1.33  
% 2.30/1.33  #Partial instantiations: 0
% 2.30/1.33  #Strategies tried      : 1
% 2.30/1.33  
% 2.30/1.33  Timing (in seconds)
% 2.30/1.33  ----------------------
% 2.30/1.34  Preprocessing        : 0.30
% 2.30/1.34  Parsing              : 0.16
% 2.30/1.34  CNF conversion       : 0.01
% 2.30/1.34  Main loop            : 0.21
% 2.30/1.34  Inferencing          : 0.07
% 2.30/1.34  Reduction            : 0.08
% 2.30/1.34  Demodulation         : 0.06
% 2.30/1.34  BG Simplification    : 0.01
% 2.30/1.34  Subsumption          : 0.04
% 2.30/1.34  Abstraction          : 0.01
% 2.30/1.34  MUC search           : 0.00
% 2.30/1.34  Cooper               : 0.00
% 2.30/1.34  Total                : 0.53
% 2.30/1.34  Index Insertion      : 0.00
% 2.30/1.34  Index Deletion       : 0.00
% 2.30/1.34  Index Matching       : 0.00
% 2.30/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
