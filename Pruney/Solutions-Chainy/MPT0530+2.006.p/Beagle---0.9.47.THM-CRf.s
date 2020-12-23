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
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  56 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_318,plain,(
    ! [A_54,B_55] :
      ( k8_relat_1(A_54,B_55) = B_55
      | ~ r1_tarski(k2_relat_1(B_55),A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_338,plain,(
    ! [A_54,A_19] :
      ( k8_relat_1(A_54,k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_54)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_318])).

tff(c_344,plain,(
    ! [A_56,A_57] :
      ( k8_relat_1(A_56,k6_relat_1(A_57)) = k6_relat_1(A_57)
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_338])).

tff(c_114,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(k2_relat_1(B_36),A_37) = k2_relat_1(k8_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [A_37,A_19] :
      ( k2_relat_1(k8_relat_1(A_37,k6_relat_1(A_19))) = k3_xboole_0(A_19,A_37)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_127,plain,(
    ! [A_37,A_19] : k2_relat_1(k8_relat_1(A_37,k6_relat_1(A_19))) = k3_xboole_0(A_19,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_123])).

tff(c_354,plain,(
    ! [A_57,A_56] :
      ( k3_xboole_0(A_57,A_56) = k2_relat_1(k6_relat_1(A_57))
      | ~ r1_tarski(A_57,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_127])).

tff(c_400,plain,(
    ! [A_58,A_59] :
      ( k3_xboole_0(A_58,A_59) = A_58
      | ~ r1_tarski(A_58,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_354])).

tff(c_429,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_400])).

tff(c_659,plain,(
    ! [A_69,B_70,C_71] :
      ( k8_relat_1(k3_xboole_0(A_69,B_70),C_71) = k8_relat_1(A_69,k8_relat_1(B_70,C_71))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1026,plain,(
    ! [C_90] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_90)) = k8_relat_1('#skF_1',C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_659])).

tff(c_24,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1048,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_24])).

tff(c_1072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1048])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:26:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.36  
% 2.53/1.36  %Foreground sorts:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Background operators:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Foreground operators:
% 2.53/1.36  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.36  
% 2.53/1.37  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 2.53/1.37  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.53/1.37  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.53/1.37  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.53/1.37  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.53/1.37  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 2.53/1.37  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.37  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.37  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.37  tff(c_6, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.37  tff(c_318, plain, (![A_54, B_55]: (k8_relat_1(A_54, B_55)=B_55 | ~r1_tarski(k2_relat_1(B_55), A_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.37  tff(c_338, plain, (![A_54, A_19]: (k8_relat_1(A_54, k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_54) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_318])).
% 2.53/1.37  tff(c_344, plain, (![A_56, A_57]: (k8_relat_1(A_56, k6_relat_1(A_57))=k6_relat_1(A_57) | ~r1_tarski(A_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_338])).
% 2.53/1.37  tff(c_114, plain, (![B_36, A_37]: (k3_xboole_0(k2_relat_1(B_36), A_37)=k2_relat_1(k8_relat_1(A_37, B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.37  tff(c_123, plain, (![A_37, A_19]: (k2_relat_1(k8_relat_1(A_37, k6_relat_1(A_19)))=k3_xboole_0(A_19, A_37) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_114])).
% 2.53/1.37  tff(c_127, plain, (![A_37, A_19]: (k2_relat_1(k8_relat_1(A_37, k6_relat_1(A_19)))=k3_xboole_0(A_19, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_123])).
% 2.53/1.37  tff(c_354, plain, (![A_57, A_56]: (k3_xboole_0(A_57, A_56)=k2_relat_1(k6_relat_1(A_57)) | ~r1_tarski(A_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_344, c_127])).
% 2.53/1.37  tff(c_400, plain, (![A_58, A_59]: (k3_xboole_0(A_58, A_59)=A_58 | ~r1_tarski(A_58, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_354])).
% 2.53/1.37  tff(c_429, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_400])).
% 2.53/1.37  tff(c_659, plain, (![A_69, B_70, C_71]: (k8_relat_1(k3_xboole_0(A_69, B_70), C_71)=k8_relat_1(A_69, k8_relat_1(B_70, C_71)) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.37  tff(c_1026, plain, (![C_90]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_90))=k8_relat_1('#skF_1', C_90) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_429, c_659])).
% 2.53/1.37  tff(c_24, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.37  tff(c_1048, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1026, c_24])).
% 2.53/1.37  tff(c_1072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1048])).
% 2.53/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  Inference rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Ref     : 0
% 2.53/1.37  #Sup     : 240
% 2.53/1.37  #Fact    : 0
% 2.53/1.37  #Define  : 0
% 2.53/1.37  #Split   : 0
% 2.53/1.37  #Chain   : 0
% 2.53/1.37  #Close   : 0
% 2.53/1.37  
% 2.53/1.37  Ordering : KBO
% 2.53/1.37  
% 2.53/1.37  Simplification rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Subsume      : 22
% 2.53/1.37  #Demod        : 143
% 2.53/1.37  #Tautology    : 114
% 2.53/1.37  #SimpNegUnit  : 0
% 2.53/1.37  #BackRed      : 0
% 2.53/1.37  
% 2.53/1.37  #Partial instantiations: 0
% 2.53/1.37  #Strategies tried      : 1
% 2.53/1.37  
% 2.53/1.37  Timing (in seconds)
% 2.53/1.37  ----------------------
% 2.53/1.37  Preprocessing        : 0.28
% 2.53/1.37  Parsing              : 0.15
% 2.53/1.37  CNF conversion       : 0.02
% 2.53/1.37  Main loop            : 0.32
% 2.53/1.37  Inferencing          : 0.13
% 2.53/1.37  Reduction            : 0.10
% 2.53/1.38  Demodulation         : 0.08
% 2.53/1.38  BG Simplification    : 0.02
% 2.53/1.38  Subsumption          : 0.06
% 2.53/1.38  Abstraction          : 0.02
% 2.53/1.38  MUC search           : 0.00
% 2.53/1.38  Cooper               : 0.00
% 2.53/1.38  Total                : 0.63
% 2.53/1.38  Index Insertion      : 0.00
% 2.53/1.38  Index Deletion       : 0.00
% 2.53/1.38  Index Matching       : 0.00
% 2.53/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
