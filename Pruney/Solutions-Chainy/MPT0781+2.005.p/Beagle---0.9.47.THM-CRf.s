%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:44 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_17,B_16] : r1_tarski(A_17,k2_xboole_0(B_16,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_105,plain,(
    ! [A_26] :
      ( r1_tarski(k2_relat_1(A_26),k3_relat_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_35])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k8_relat_1(A_8,B_9) = B_9
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_26] :
      ( k8_relat_1(k3_relat_1(A_26),A_26) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_105,c_10])).

tff(c_166,plain,(
    ! [A_32,B_33] :
      ( k7_relat_1(k8_relat_1(A_32,B_33),A_32) = k2_wellord1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_255,plain,(
    ! [A_41] :
      ( k7_relat_1(A_41,k3_relat_1(A_41)) = k2_wellord1(A_41,k3_relat_1(A_41))
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_166])).

tff(c_87,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(A_22),k3_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_184,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_196,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k3_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_87,c_184])).

tff(c_270,plain,(
    ! [A_42] :
      ( k2_wellord1(A_42,k3_relat_1(A_42)) = A_42
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_196])).

tff(c_16,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_276,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_16])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 2.02/1.28  
% 2.02/1.28  %Foreground sorts:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Background operators:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Foreground operators:
% 2.02/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.02/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.02/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.28  
% 2.02/1.29  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 2.02/1.29  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.02/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.02/1.29  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.02/1.29  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.02/1.29  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 2.02/1.29  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.02/1.29  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.29  tff(c_78, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.29  tff(c_20, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.29  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.29  tff(c_35, plain, (![A_17, B_16]: (r1_tarski(A_17, k2_xboole_0(B_16, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 2.02/1.29  tff(c_105, plain, (![A_26]: (r1_tarski(k2_relat_1(A_26), k3_relat_1(A_26)) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_78, c_35])).
% 2.02/1.29  tff(c_10, plain, (![A_8, B_9]: (k8_relat_1(A_8, B_9)=B_9 | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.29  tff(c_109, plain, (![A_26]: (k8_relat_1(k3_relat_1(A_26), A_26)=A_26 | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_105, c_10])).
% 2.02/1.29  tff(c_166, plain, (![A_32, B_33]: (k7_relat_1(k8_relat_1(A_32, B_33), A_32)=k2_wellord1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.29  tff(c_255, plain, (![A_41]: (k7_relat_1(A_41, k3_relat_1(A_41))=k2_wellord1(A_41, k3_relat_1(A_41)) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_109, c_166])).
% 2.02/1.29  tff(c_87, plain, (![A_22]: (r1_tarski(k1_relat_1(A_22), k3_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 2.02/1.29  tff(c_184, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.29  tff(c_196, plain, (![A_22]: (k7_relat_1(A_22, k3_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_87, c_184])).
% 2.02/1.29  tff(c_270, plain, (![A_42]: (k2_wellord1(A_42, k3_relat_1(A_42))=A_42 | ~v1_relat_1(A_42) | ~v1_relat_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_255, c_196])).
% 2.02/1.29  tff(c_16, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.29  tff(c_276, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_270, c_16])).
% 2.02/1.29  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_276])).
% 2.02/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  Inference rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Ref     : 0
% 2.02/1.29  #Sup     : 62
% 2.02/1.29  #Fact    : 0
% 2.02/1.29  #Define  : 0
% 2.02/1.29  #Split   : 0
% 2.02/1.29  #Chain   : 0
% 2.02/1.29  #Close   : 0
% 2.02/1.29  
% 2.02/1.29  Ordering : KBO
% 2.02/1.29  
% 2.02/1.29  Simplification rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Subsume      : 10
% 2.02/1.29  #Demod        : 4
% 2.02/1.29  #Tautology    : 36
% 2.02/1.29  #SimpNegUnit  : 0
% 2.02/1.29  #BackRed      : 0
% 2.02/1.29  
% 2.02/1.29  #Partial instantiations: 0
% 2.02/1.29  #Strategies tried      : 1
% 2.02/1.29  
% 2.02/1.29  Timing (in seconds)
% 2.02/1.29  ----------------------
% 2.02/1.29  Preprocessing        : 0.29
% 2.02/1.29  Parsing              : 0.16
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.18
% 2.02/1.29  Inferencing          : 0.07
% 2.02/1.29  Reduction            : 0.06
% 2.02/1.29  Demodulation         : 0.05
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.03
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.49
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
