%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  39 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [B_29,A_30] :
      ( k3_xboole_0(k1_relat_1(B_29),A_30) = k1_relat_1(k7_relat_1(B_29,A_30))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    ! [A_14,A_30] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_30)) = k3_xboole_0(A_14,A_30)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_130,plain,(
    ! [A_14,A_30] : k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_30)) = k3_xboole_0(A_14,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_187,plain,(
    ! [A_35,B_36] :
      ( k7_relat_1(A_35,k1_relat_1(k7_relat_1(B_36,k1_relat_1(A_35)))) = k7_relat_1(A_35,k1_relat_1(B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_210,plain,(
    ! [A_35,A_14] :
      ( k7_relat_1(A_35,k3_xboole_0(A_14,k1_relat_1(A_35))) = k7_relat_1(A_35,k1_relat_1(k6_relat_1(A_14)))
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_187])).

tff(c_222,plain,(
    ! [A_37,A_38] :
      ( k7_relat_1(A_37,k3_xboole_0(A_38,k1_relat_1(A_37))) = k7_relat_1(A_37,A_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_210])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_23,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_232,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_23])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  %$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.96/1.19  
% 1.96/1.19  %Foreground sorts:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Background operators:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Foreground operators:
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.19  
% 1.96/1.20  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.96/1.20  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.96/1.20  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.96/1.20  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.96/1.20  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 1.96/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.96/1.20  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.20  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.20  tff(c_14, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.20  tff(c_103, plain, (![B_29, A_30]: (k3_xboole_0(k1_relat_1(B_29), A_30)=k1_relat_1(k7_relat_1(B_29, A_30)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.96/1.20  tff(c_126, plain, (![A_14, A_30]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_30))=k3_xboole_0(A_14, A_30) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 1.96/1.20  tff(c_130, plain, (![A_14, A_30]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_30))=k3_xboole_0(A_14, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_126])).
% 1.96/1.20  tff(c_187, plain, (![A_35, B_36]: (k7_relat_1(A_35, k1_relat_1(k7_relat_1(B_36, k1_relat_1(A_35))))=k7_relat_1(A_35, k1_relat_1(B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.20  tff(c_210, plain, (![A_35, A_14]: (k7_relat_1(A_35, k3_xboole_0(A_14, k1_relat_1(A_35)))=k7_relat_1(A_35, k1_relat_1(k6_relat_1(A_14))) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_130, c_187])).
% 1.96/1.20  tff(c_222, plain, (![A_37, A_38]: (k7_relat_1(A_37, k3_xboole_0(A_38, k1_relat_1(A_37)))=k7_relat_1(A_37, A_38) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_210])).
% 1.96/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.20  tff(c_20, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.20  tff(c_23, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.96/1.20  tff(c_232, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_222, c_23])).
% 1.96/1.20  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_232])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 0
% 1.96/1.20  #Sup     : 57
% 1.96/1.20  #Fact    : 0
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 0
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 8
% 1.96/1.20  #Demod        : 15
% 1.96/1.20  #Tautology    : 27
% 1.96/1.20  #SimpNegUnit  : 0
% 1.96/1.20  #BackRed      : 0
% 1.96/1.20  
% 1.96/1.20  #Partial instantiations: 0
% 1.96/1.20  #Strategies tried      : 1
% 1.96/1.20  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 1.96/1.20  Preprocessing        : 0.29
% 1.96/1.20  Parsing              : 0.15
% 1.96/1.20  CNF conversion       : 0.02
% 1.96/1.20  Main loop            : 0.16
% 1.96/1.20  Inferencing          : 0.06
% 1.96/1.20  Reduction            : 0.06
% 1.96/1.20  Demodulation         : 0.05
% 1.96/1.20  BG Simplification    : 0.01
% 2.02/1.20  Subsumption          : 0.02
% 2.02/1.20  Abstraction          : 0.01
% 2.02/1.20  MUC search           : 0.00
% 2.02/1.20  Cooper               : 0.00
% 2.02/1.20  Total                : 0.48
% 2.02/1.20  Index Insertion      : 0.00
% 2.02/1.20  Index Deletion       : 0.00
% 2.02/1.20  Index Matching       : 0.00
% 2.02/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
