%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  45 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(C_13,k6_subset_1(A_11,B_12)) = k6_subset_1(C_13,k7_relat_1(C_13,B_12))
      | ~ r1_tarski(k1_relat_1(C_13),A_11)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [C_36,A_37,B_38] :
      ( k7_relat_1(C_36,k4_xboole_0(A_37,B_38)) = k4_xboole_0(C_36,k7_relat_1(C_36,B_38))
      | ~ r1_tarski(k1_relat_1(C_36),A_37)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_186,plain,(
    ! [C_39,B_40] :
      ( k7_relat_1(C_39,k4_xboole_0(k1_relat_1(C_39),B_40)) = k4_xboole_0(C_39,k7_relat_1(C_39,B_40))
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [B_31,A_32] :
      ( k1_relat_1(k7_relat_1(B_31,A_32)) = A_32
      | ~ r1_tarski(A_32,k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    ! [B_31,B_8] :
      ( k1_relat_1(k7_relat_1(B_31,k4_xboole_0(k1_relat_1(B_31),B_8))) = k4_xboole_0(k1_relat_1(B_31),B_8)
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

tff(c_204,plain,(
    ! [C_41,B_42] :
      ( k1_relat_1(k4_xboole_0(C_41,k7_relat_1(C_41,B_42))) = k4_xboole_0(k1_relat_1(C_41),B_42)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_133])).

tff(c_20,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_224,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_23])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n003.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 11:14:27 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.06  
% 1.69/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.07  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.69/1.07  
% 1.69/1.07  %Foreground sorts:
% 1.69/1.07  
% 1.69/1.07  
% 1.69/1.07  %Background operators:
% 1.69/1.07  
% 1.69/1.07  
% 1.69/1.07  %Foreground operators:
% 1.69/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.07  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.69/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.07  
% 1.69/1.07  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 1.69/1.07  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.07  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.69/1.07  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 1.69/1.07  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.69/1.07  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.69/1.07  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.07  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.07  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.07  tff(c_16, plain, (![C_13, A_11, B_12]: (k7_relat_1(C_13, k6_subset_1(A_11, B_12))=k6_subset_1(C_13, k7_relat_1(C_13, B_12)) | ~r1_tarski(k1_relat_1(C_13), A_11) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.07  tff(c_177, plain, (![C_36, A_37, B_38]: (k7_relat_1(C_36, k4_xboole_0(A_37, B_38))=k4_xboole_0(C_36, k7_relat_1(C_36, B_38)) | ~r1_tarski(k1_relat_1(C_36), A_37) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 1.69/1.07  tff(c_186, plain, (![C_39, B_40]: (k7_relat_1(C_39, k4_xboole_0(k1_relat_1(C_39), B_40))=k4_xboole_0(C_39, k7_relat_1(C_39, B_40)) | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_8, c_177])).
% 1.69/1.07  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.07  tff(c_124, plain, (![B_31, A_32]: (k1_relat_1(k7_relat_1(B_31, A_32))=A_32 | ~r1_tarski(A_32, k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.69/1.07  tff(c_133, plain, (![B_31, B_8]: (k1_relat_1(k7_relat_1(B_31, k4_xboole_0(k1_relat_1(B_31), B_8)))=k4_xboole_0(k1_relat_1(B_31), B_8) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_12, c_124])).
% 1.69/1.07  tff(c_204, plain, (![C_41, B_42]: (k1_relat_1(k4_xboole_0(C_41, k7_relat_1(C_41, B_42)))=k4_xboole_0(k1_relat_1(C_41), B_42) | ~v1_relat_1(C_41) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_186, c_133])).
% 1.69/1.07  tff(c_20, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.07  tff(c_23, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 1.69/1.07  tff(c_224, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_204, c_23])).
% 1.69/1.07  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_224])).
% 1.69/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.07  
% 1.69/1.07  Inference rules
% 1.69/1.07  ----------------------
% 1.69/1.07  #Ref     : 0
% 1.69/1.07  #Sup     : 53
% 1.69/1.07  #Fact    : 0
% 1.69/1.07  #Define  : 0
% 1.69/1.07  #Split   : 0
% 1.69/1.07  #Chain   : 0
% 1.69/1.07  #Close   : 0
% 1.69/1.07  
% 1.69/1.07  Ordering : KBO
% 1.69/1.07  
% 1.69/1.07  Simplification rules
% 1.69/1.07  ----------------------
% 1.69/1.07  #Subsume      : 0
% 1.69/1.07  #Demod        : 10
% 1.69/1.07  #Tautology    : 28
% 1.69/1.07  #SimpNegUnit  : 0
% 1.69/1.08  #BackRed      : 0
% 1.69/1.08  
% 1.69/1.08  #Partial instantiations: 0
% 1.69/1.08  #Strategies tried      : 1
% 1.69/1.08  
% 1.69/1.08  Timing (in seconds)
% 1.69/1.08  ----------------------
% 1.69/1.08  Preprocessing        : 0.28
% 1.69/1.08  Parsing              : 0.15
% 1.69/1.08  CNF conversion       : 0.02
% 1.69/1.08  Main loop            : 0.15
% 1.69/1.08  Inferencing          : 0.06
% 1.69/1.08  Reduction            : 0.05
% 1.69/1.08  Demodulation         : 0.04
% 1.69/1.08  BG Simplification    : 0.01
% 1.69/1.08  Subsumption          : 0.03
% 1.69/1.08  Abstraction          : 0.01
% 1.69/1.08  MUC search           : 0.00
% 1.69/1.08  Cooper               : 0.00
% 1.69/1.08  Total                : 0.46
% 1.69/1.08  Index Insertion      : 0.00
% 1.69/1.08  Index Deletion       : 0.00
% 1.69/1.08  Index Matching       : 0.00
% 1.69/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
