%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k8_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_76,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_76])).

tff(c_97,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_122,plain,(
    ! [A_33,B_34,C_35] :
      ( k8_relat_1(k3_xboole_0(A_33,B_34),C_35) = k8_relat_1(A_33,k8_relat_1(B_34,C_35))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [C_38] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_38)) = k8_relat_1('#skF_1',C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_122])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k8_relat_1(A_12,B_13),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_313,plain,(
    ! [C_48] :
      ( r1_tarski(k8_relat_1('#skF_1',C_48),k8_relat_1('#skF_2',C_48))
      | ~ v1_relat_1(k8_relat_1('#skF_2',C_48))
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_16])).

tff(c_20,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_316,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_20])).

tff(c_325,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_316])).

tff(c_329,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_325])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.27  
% 1.96/1.27  %Foreground sorts:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Background operators:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Foreground operators:
% 1.96/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.27  
% 1.96/1.28  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 1.96/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.96/1.28  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.96/1.28  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.96/1.28  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.96/1.28  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 1.96/1.28  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.96/1.28  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.28  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k8_relat_1(A_10, B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.28  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.28  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.28  tff(c_35, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.28  tff(c_39, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_35])).
% 1.96/1.28  tff(c_76, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.28  tff(c_91, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_39, c_76])).
% 1.96/1.28  tff(c_97, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_91])).
% 1.96/1.28  tff(c_122, plain, (![A_33, B_34, C_35]: (k8_relat_1(k3_xboole_0(A_33, B_34), C_35)=k8_relat_1(A_33, k8_relat_1(B_34, C_35)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.28  tff(c_172, plain, (![C_38]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_38))=k8_relat_1('#skF_1', C_38) | ~v1_relat_1(C_38))), inference(superposition, [status(thm), theory('equality')], [c_97, c_122])).
% 1.96/1.28  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k8_relat_1(A_12, B_13), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.28  tff(c_313, plain, (![C_48]: (r1_tarski(k8_relat_1('#skF_1', C_48), k8_relat_1('#skF_2', C_48)) | ~v1_relat_1(k8_relat_1('#skF_2', C_48)) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_172, c_16])).
% 1.96/1.28  tff(c_20, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.28  tff(c_316, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_313, c_20])).
% 1.96/1.28  tff(c_325, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_316])).
% 1.96/1.28  tff(c_329, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_325])).
% 1.96/1.28  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_329])).
% 1.96/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  
% 1.96/1.28  Inference rules
% 1.96/1.28  ----------------------
% 1.96/1.28  #Ref     : 0
% 1.96/1.28  #Sup     : 78
% 1.96/1.28  #Fact    : 0
% 1.96/1.28  #Define  : 0
% 1.96/1.28  #Split   : 1
% 1.96/1.28  #Chain   : 0
% 1.96/1.28  #Close   : 0
% 1.96/1.28  
% 1.96/1.28  Ordering : KBO
% 1.96/1.28  
% 1.96/1.28  Simplification rules
% 1.96/1.28  ----------------------
% 1.96/1.28  #Subsume      : 4
% 1.96/1.28  #Demod        : 24
% 1.96/1.28  #Tautology    : 43
% 1.96/1.28  #SimpNegUnit  : 0
% 1.96/1.28  #BackRed      : 0
% 1.96/1.28  
% 1.96/1.28  #Partial instantiations: 0
% 1.96/1.28  #Strategies tried      : 1
% 1.96/1.28  
% 1.96/1.28  Timing (in seconds)
% 1.96/1.28  ----------------------
% 1.96/1.28  Preprocessing        : 0.28
% 1.96/1.28  Parsing              : 0.15
% 1.96/1.28  CNF conversion       : 0.02
% 1.96/1.28  Main loop            : 0.21
% 1.96/1.29  Inferencing          : 0.09
% 1.96/1.29  Reduction            : 0.06
% 1.96/1.29  Demodulation         : 0.05
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.03
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.51
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
