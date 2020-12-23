%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:58 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  38 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_26,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_85,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_20,plain,(
    ! [A_33,B_34] : k6_subset_1(A_33,B_34) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [C_39,A_37,B_38] :
      ( k6_subset_1(k7_relat_1(C_39,A_37),k7_relat_1(C_39,B_38)) = k7_relat_1(C_39,k6_subset_1(A_37,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [C_63,A_64,B_65] :
      ( k4_xboole_0(k7_relat_1(C_63,A_64),k7_relat_1(C_63,B_65)) = k7_relat_1(C_63,k4_xboole_0(A_64,B_65))
      | ~ v1_relat_1(C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_24])).

tff(c_127,plain,(
    ! [C_63,B_65] :
      ( k7_relat_1(C_63,k4_xboole_0(B_65,B_65)) = k1_xboole_0
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_85])).

tff(c_139,plain,(
    ! [C_66] :
      ( k7_relat_1(C_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_127])).

tff(c_142,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:51:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.22  
% 1.99/1.23  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.99/1.23  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.99/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.99/1.23  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.99/1.23  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.99/1.23  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 1.99/1.23  tff(c_26, plain, (k7_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.23  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.23  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.23  tff(c_73, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.23  tff(c_82, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 1.99/1.23  tff(c_85, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82])).
% 1.99/1.23  tff(c_20, plain, (![A_33, B_34]: (k6_subset_1(A_33, B_34)=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.23  tff(c_24, plain, (![C_39, A_37, B_38]: (k6_subset_1(k7_relat_1(C_39, A_37), k7_relat_1(C_39, B_38))=k7_relat_1(C_39, k6_subset_1(A_37, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.23  tff(c_120, plain, (![C_63, A_64, B_65]: (k4_xboole_0(k7_relat_1(C_63, A_64), k7_relat_1(C_63, B_65))=k7_relat_1(C_63, k4_xboole_0(A_64, B_65)) | ~v1_relat_1(C_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_24])).
% 1.99/1.23  tff(c_127, plain, (![C_63, B_65]: (k7_relat_1(C_63, k4_xboole_0(B_65, B_65))=k1_xboole_0 | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_120, c_85])).
% 1.99/1.23  tff(c_139, plain, (![C_66]: (k7_relat_1(C_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_66))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_127])).
% 1.99/1.23  tff(c_142, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_139])).
% 1.99/1.23  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_142])).
% 1.99/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  Inference rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Ref     : 0
% 1.99/1.23  #Sup     : 26
% 1.99/1.23  #Fact    : 0
% 1.99/1.23  #Define  : 0
% 1.99/1.23  #Split   : 0
% 1.99/1.23  #Chain   : 0
% 1.99/1.23  #Close   : 0
% 1.99/1.23  
% 1.99/1.23  Ordering : KBO
% 1.99/1.23  
% 1.99/1.23  Simplification rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Subsume      : 0
% 1.99/1.23  #Demod        : 5
% 1.99/1.23  #Tautology    : 22
% 1.99/1.23  #SimpNegUnit  : 1
% 1.99/1.23  #BackRed      : 0
% 1.99/1.23  
% 1.99/1.23  #Partial instantiations: 0
% 1.99/1.23  #Strategies tried      : 1
% 1.99/1.23  
% 1.99/1.23  Timing (in seconds)
% 1.99/1.23  ----------------------
% 1.99/1.23  Preprocessing        : 0.32
% 1.99/1.23  Parsing              : 0.17
% 1.99/1.23  CNF conversion       : 0.02
% 1.99/1.23  Main loop            : 0.11
% 1.99/1.23  Inferencing          : 0.04
% 1.99/1.23  Reduction            : 0.04
% 1.99/1.23  Demodulation         : 0.03
% 1.99/1.23  BG Simplification    : 0.01
% 1.99/1.23  Subsumption          : 0.01
% 1.99/1.23  Abstraction          : 0.01
% 1.99/1.23  MUC search           : 0.00
% 1.99/1.23  Cooper               : 0.00
% 1.99/1.23  Total                : 0.45
% 1.99/1.23  Index Insertion      : 0.00
% 1.99/1.23  Index Deletion       : 0.00
% 1.99/1.23  Index Matching       : 0.00
% 1.99/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
