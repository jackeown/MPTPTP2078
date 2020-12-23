%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k6_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_18,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [B_20,C_21] : r1_tarski(k4_xboole_0(B_20,C_21),B_20) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_finset_1(A_8)
      | ~ v1_finset_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [B_22,C_23] :
      ( v1_finset_1(k4_xboole_0(B_22,C_23))
      | ~ v1_finset_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_49,c_14])).

tff(c_12,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ~ v1_finset_1(k6_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    ~ v1_finset_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_65,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_19])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  %$ r1_xboole_0 > r1_tarski > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.63/1.15  
% 1.63/1.15  %Foreground sorts:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Background operators:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Foreground operators:
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.63/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.15  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.63/1.15  
% 1.63/1.16  tff(f_50, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k6_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_finset_1)).
% 1.63/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.16  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.63/1.16  tff(f_45, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 1.63/1.16  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.63/1.16  tff(c_18, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.16  tff(c_43, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, B_18) | ~r1_tarski(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.16  tff(c_49, plain, (![B_20, C_21]: (r1_tarski(k4_xboole_0(B_20, C_21), B_20))), inference(resolution, [status(thm)], [c_6, c_43])).
% 1.63/1.16  tff(c_14, plain, (![A_8, B_9]: (v1_finset_1(A_8) | ~v1_finset_1(B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.16  tff(c_62, plain, (![B_22, C_23]: (v1_finset_1(k4_xboole_0(B_22, C_23)) | ~v1_finset_1(B_22))), inference(resolution, [status(thm)], [c_49, c_14])).
% 1.63/1.16  tff(c_12, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.16  tff(c_16, plain, (~v1_finset_1(k6_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.16  tff(c_19, plain, (~v1_finset_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 1.63/1.16  tff(c_65, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_62, c_19])).
% 1.63/1.16  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_65])).
% 1.63/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  Inference rules
% 1.63/1.16  ----------------------
% 1.63/1.16  #Ref     : 0
% 1.63/1.16  #Sup     : 9
% 1.63/1.16  #Fact    : 0
% 1.63/1.16  #Define  : 0
% 1.63/1.16  #Split   : 0
% 1.63/1.16  #Chain   : 0
% 1.63/1.16  #Close   : 0
% 1.63/1.16  
% 1.63/1.16  Ordering : KBO
% 1.63/1.16  
% 1.63/1.16  Simplification rules
% 1.63/1.16  ----------------------
% 1.63/1.16  #Subsume      : 0
% 1.63/1.16  #Demod        : 4
% 1.63/1.16  #Tautology    : 5
% 1.63/1.16  #SimpNegUnit  : 0
% 1.63/1.16  #BackRed      : 0
% 1.63/1.16  
% 1.63/1.16  #Partial instantiations: 0
% 1.63/1.16  #Strategies tried      : 1
% 1.63/1.16  
% 1.63/1.16  Timing (in seconds)
% 1.63/1.16  ----------------------
% 1.63/1.16  Preprocessing        : 0.29
% 1.63/1.16  Parsing              : 0.16
% 1.63/1.16  CNF conversion       : 0.02
% 1.63/1.16  Main loop            : 0.08
% 1.63/1.17  Inferencing          : 0.03
% 1.63/1.17  Reduction            : 0.03
% 1.63/1.17  Demodulation         : 0.02
% 1.63/1.17  BG Simplification    : 0.01
% 1.63/1.17  Subsumption          : 0.01
% 1.63/1.17  Abstraction          : 0.01
% 1.63/1.17  MUC search           : 0.00
% 1.63/1.17  Cooper               : 0.00
% 1.63/1.17  Total                : 0.39
% 1.63/1.17  Index Insertion      : 0.00
% 1.63/1.17  Index Deletion       : 0.00
% 1.63/1.17  Index Matching       : 0.00
% 1.63/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
