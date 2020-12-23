%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  48 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k6_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_36,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(k5_xboole_0(A_69,C_70),B_71)
      | ~ r1_tarski(C_70,B_71)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( v1_finset_1(A_43)
      | ~ v1_finset_1(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_171,plain,(
    ! [A_76,C_77,B_78] :
      ( v1_finset_1(k5_xboole_0(A_76,C_77))
      | ~ v1_finset_1(B_78)
      | ~ r1_tarski(C_77,B_78)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(resolution,[status(thm)],[c_140,c_32])).

tff(c_181,plain,(
    ! [A_79,B_80] :
      ( v1_finset_1(k5_xboole_0(A_79,B_80))
      | ~ v1_finset_1(B_80)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_191,plain,(
    ! [B_81,A_82] :
      ( v1_finset_1(k5_xboole_0(B_81,A_82))
      | ~ v1_finset_1(B_81)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_194,plain,(
    ! [A_5,B_6] :
      ( v1_finset_1(k4_xboole_0(A_5,B_6))
      | ~ v1_finset_1(A_5)
      | ~ r1_tarski(k3_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_212,plain,(
    ! [A_88,B_89] :
      ( v1_finset_1(k4_xboole_0(A_88,B_89))
      | ~ v1_finset_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_194])).

tff(c_28,plain,(
    ! [A_39,B_40] : k6_subset_1(A_39,B_40) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ~ v1_finset_1(k6_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_37,plain,(
    ~ v1_finset_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_215,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_212,c_37])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r1_tarski > v1_finset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.30  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.12/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.30  
% 2.12/1.31  tff(f_70, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k6_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_finset_1)).
% 2.12/1.31  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.12/1.31  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.12/1.31  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.12/1.31  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.31  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.12/1.31  tff(f_65, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 2.12/1.31  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.12/1.31  tff(c_36, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.31  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.31  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.31  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.31  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_140, plain, (![A_69, C_70, B_71]: (r1_tarski(k5_xboole_0(A_69, C_70), B_71) | ~r1_tarski(C_70, B_71) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.31  tff(c_32, plain, (![A_43, B_44]: (v1_finset_1(A_43) | ~v1_finset_1(B_44) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.31  tff(c_171, plain, (![A_76, C_77, B_78]: (v1_finset_1(k5_xboole_0(A_76, C_77)) | ~v1_finset_1(B_78) | ~r1_tarski(C_77, B_78) | ~r1_tarski(A_76, B_78))), inference(resolution, [status(thm)], [c_140, c_32])).
% 2.12/1.31  tff(c_181, plain, (![A_79, B_80]: (v1_finset_1(k5_xboole_0(A_79, B_80)) | ~v1_finset_1(B_80) | ~r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_8, c_171])).
% 2.12/1.31  tff(c_191, plain, (![B_81, A_82]: (v1_finset_1(k5_xboole_0(B_81, A_82)) | ~v1_finset_1(B_81) | ~r1_tarski(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 2.12/1.31  tff(c_194, plain, (![A_5, B_6]: (v1_finset_1(k4_xboole_0(A_5, B_6)) | ~v1_finset_1(A_5) | ~r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_191])).
% 2.12/1.31  tff(c_212, plain, (![A_88, B_89]: (v1_finset_1(k4_xboole_0(A_88, B_89)) | ~v1_finset_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_194])).
% 2.12/1.31  tff(c_28, plain, (![A_39, B_40]: (k6_subset_1(A_39, B_40)=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.31  tff(c_34, plain, (~v1_finset_1(k6_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.31  tff(c_37, plain, (~v1_finset_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 2.12/1.31  tff(c_215, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_212, c_37])).
% 2.12/1.31  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_215])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 42
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 0
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 4
% 2.12/1.31  #Demod        : 5
% 2.12/1.31  #Tautology    : 25
% 2.12/1.31  #SimpNegUnit  : 0
% 2.12/1.31  #BackRed      : 0
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.31  Preprocessing        : 0.35
% 2.12/1.31  Parsing              : 0.19
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.15
% 2.12/1.31  Inferencing          : 0.06
% 2.12/1.31  Reduction            : 0.05
% 2.12/1.31  Demodulation         : 0.04
% 2.12/1.31  BG Simplification    : 0.02
% 2.12/1.31  Subsumption          : 0.03
% 2.12/1.31  Abstraction          : 0.01
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.53
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
