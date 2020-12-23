%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(k7_relat_1(B_35,A_36),k1_relat_1(B_35)) = k7_relat_1(B_35,A_36)
      | ~ v1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k7_relat_1(C_11,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,k3_xboole_0(A_41,k1_relat_1(B_40))) = k7_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k7_relat_1(B_40,A_41))
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_6])).

tff(c_16,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_100,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_16])).

tff(c_242,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_100])).

tff(c_264,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_242])).

tff(c_268,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_264])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:03:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.08/1.28  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.08/1.28  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.08/1.28  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.08/1.28  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.08/1.28  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.08/1.28  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.08/1.28  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.28  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.28  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.28  tff(c_136, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.28  tff(c_162, plain, (![B_35, A_36]: (k7_relat_1(k7_relat_1(B_35, A_36), k1_relat_1(B_35))=k7_relat_1(B_35, A_36) | ~v1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_12, c_136])).
% 2.08/1.28  tff(c_10, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k7_relat_1(C_11, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.28  tff(c_217, plain, (![B_40, A_41]: (k7_relat_1(B_40, k3_xboole_0(A_41, k1_relat_1(B_40)))=k7_relat_1(B_40, A_41) | ~v1_relat_1(B_40) | ~v1_relat_1(k7_relat_1(B_40, A_41)) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_162, c_10])).
% 2.08/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.28  tff(c_62, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.28  tff(c_77, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62])).
% 2.08/1.28  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.28  tff(c_83, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_77, c_6])).
% 2.08/1.28  tff(c_16, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.28  tff(c_100, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_16])).
% 2.08/1.28  tff(c_242, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_217, c_100])).
% 2.08/1.28  tff(c_264, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_242])).
% 2.08/1.28  tff(c_268, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_264])).
% 2.08/1.28  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_268])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 65
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 7
% 2.08/1.28  #Demod        : 6
% 2.08/1.28  #Tautology    : 31
% 2.08/1.28  #SimpNegUnit  : 0
% 2.08/1.28  #BackRed      : 1
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.29
% 2.08/1.28  Parsing              : 0.16
% 2.08/1.28  CNF conversion       : 0.01
% 2.08/1.28  Main loop            : 0.18
% 2.08/1.28  Inferencing          : 0.07
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.05
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.03
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.50
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
