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
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_49] :
      ( k7_relat_1(A_49,k1_relat_1(A_49)) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_36,B_37] : k6_subset_1(A_36,B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [C_44,A_42,B_43] :
      ( k6_subset_1(k7_relat_1(C_44,A_42),k7_relat_1(C_44,B_43)) = k7_relat_1(C_44,k6_subset_1(A_42,B_43))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_404,plain,(
    ! [C_103,A_104,B_105] :
      ( k4_xboole_0(k7_relat_1(C_103,A_104),k7_relat_1(C_103,B_105)) = k7_relat_1(C_103,k4_xboole_0(A_104,B_105))
      | ~ v1_relat_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_32])).

tff(c_621,plain,(
    ! [A_121,B_122] :
      ( k7_relat_1(A_121,k4_xboole_0(k1_relat_1(A_121),B_122)) = k4_xboole_0(A_121,k7_relat_1(A_121,B_122))
      | ~ v1_relat_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_404])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(k7_relat_1(B_79,A_80)) = A_80
      | ~ r1_tarski(A_80,k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_259,plain,(
    ! [B_79,B_8] :
      ( k1_relat_1(k7_relat_1(B_79,k4_xboole_0(k1_relat_1(B_79),B_8))) = k4_xboole_0(k1_relat_1(B_79),B_8)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_12,c_250])).

tff(c_783,plain,(
    ! [A_132,B_133] :
      ( k1_relat_1(k4_xboole_0(A_132,k7_relat_1(A_132,B_133))) = k4_xboole_0(k1_relat_1(A_132),B_133)
      | ~ v1_relat_1(A_132)
      | ~ v1_relat_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_259])).

tff(c_40,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_40])).

tff(c_831,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_43])).

tff(c_851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.76/1.41  
% 2.76/1.41  %Foreground sorts:
% 2.76/1.41  
% 2.76/1.41  
% 2.76/1.41  %Background operators:
% 2.76/1.41  
% 2.76/1.41  
% 2.76/1.41  %Foreground operators:
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.76/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.41  
% 2.76/1.42  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.76/1.42  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.76/1.42  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.76/1.42  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 2.76/1.42  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.76/1.42  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.76/1.42  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.42  tff(c_38, plain, (![A_49]: (k7_relat_1(A_49, k1_relat_1(A_49))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.42  tff(c_26, plain, (![A_36, B_37]: (k6_subset_1(A_36, B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.42  tff(c_32, plain, (![C_44, A_42, B_43]: (k6_subset_1(k7_relat_1(C_44, A_42), k7_relat_1(C_44, B_43))=k7_relat_1(C_44, k6_subset_1(A_42, B_43)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.42  tff(c_404, plain, (![C_103, A_104, B_105]: (k4_xboole_0(k7_relat_1(C_103, A_104), k7_relat_1(C_103, B_105))=k7_relat_1(C_103, k4_xboole_0(A_104, B_105)) | ~v1_relat_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_32])).
% 2.76/1.42  tff(c_621, plain, (![A_121, B_122]: (k7_relat_1(A_121, k4_xboole_0(k1_relat_1(A_121), B_122))=k4_xboole_0(A_121, k7_relat_1(A_121, B_122)) | ~v1_relat_1(A_121) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_38, c_404])).
% 2.76/1.42  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.42  tff(c_250, plain, (![B_79, A_80]: (k1_relat_1(k7_relat_1(B_79, A_80))=A_80 | ~r1_tarski(A_80, k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.42  tff(c_259, plain, (![B_79, B_8]: (k1_relat_1(k7_relat_1(B_79, k4_xboole_0(k1_relat_1(B_79), B_8)))=k4_xboole_0(k1_relat_1(B_79), B_8) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_12, c_250])).
% 2.76/1.42  tff(c_783, plain, (![A_132, B_133]: (k1_relat_1(k4_xboole_0(A_132, k7_relat_1(A_132, B_133)))=k4_xboole_0(k1_relat_1(A_132), B_133) | ~v1_relat_1(A_132) | ~v1_relat_1(A_132) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_621, c_259])).
% 2.76/1.42  tff(c_40, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.42  tff(c_43, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_40])).
% 2.76/1.42  tff(c_831, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_783, c_43])).
% 2.76/1.42  tff(c_851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_831])).
% 2.76/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  Inference rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Ref     : 0
% 2.76/1.42  #Sup     : 224
% 2.76/1.42  #Fact    : 0
% 2.76/1.42  #Define  : 0
% 2.76/1.42  #Split   : 0
% 2.76/1.42  #Chain   : 0
% 2.76/1.42  #Close   : 0
% 2.76/1.42  
% 2.76/1.42  Ordering : KBO
% 2.76/1.42  
% 2.76/1.42  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 19
% 2.76/1.42  #Demod        : 13
% 2.76/1.42  #Tautology    : 73
% 2.76/1.42  #SimpNegUnit  : 0
% 2.76/1.42  #BackRed      : 0
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.42  Preprocessing        : 0.32
% 2.76/1.42  Parsing              : 0.17
% 2.76/1.42  CNF conversion       : 0.02
% 2.76/1.42  Main loop            : 0.35
% 2.76/1.42  Inferencing          : 0.14
% 2.76/1.42  Reduction            : 0.10
% 2.76/1.42  Demodulation         : 0.07
% 2.76/1.42  BG Simplification    : 0.03
% 2.76/1.42  Subsumption          : 0.07
% 2.76/1.42  Abstraction          : 0.03
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.70
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
