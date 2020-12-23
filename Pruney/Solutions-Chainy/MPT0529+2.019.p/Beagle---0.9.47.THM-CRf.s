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
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  51 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [B_21,A_22] :
      ( k3_xboole_0(k2_relat_1(B_21),A_22) = k2_relat_1(k8_relat_1(A_22,B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_22,A_13] :
      ( k2_relat_1(k8_relat_1(A_22,k6_relat_1(A_13))) = k3_xboole_0(A_13,A_22)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_73,plain,(
    ! [A_22,A_13] : k2_relat_1(k8_relat_1(A_22,k6_relat_1(A_13))) = k3_xboole_0(A_13,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_74,plain,(
    ! [A_23,B_24] :
      ( k2_relat_1(k8_relat_1(A_23,B_24)) = A_23
      | ~ r1_tarski(A_23,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_23,A_13] :
      ( k2_relat_1(k8_relat_1(A_23,k6_relat_1(A_13))) = A_23
      | ~ r1_tarski(A_23,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_79,plain,(
    ! [A_23,A_13] :
      ( k2_relat_1(k8_relat_1(A_23,k6_relat_1(A_13))) = A_23
      | ~ r1_tarski(A_23,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_96,plain,(
    ! [A_27,A_28] :
      ( k3_xboole_0(A_27,A_28) = A_28
      | ~ r1_tarski(A_28,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_79])).

tff(c_100,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_105,plain,(
    ! [A_29,B_30,C_31] :
      ( k8_relat_1(k3_xboole_0(A_29,B_30),C_31) = k8_relat_1(A_29,k8_relat_1(B_30,C_31))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [C_32] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',C_32)) = k8_relat_1('#skF_1',C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_105])).

tff(c_18,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_132,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_18])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:30:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.71/1.13  
% 1.71/1.14  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.71/1.14  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.71/1.14  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.71/1.14  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 1.71/1.14  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 1.71/1.14  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.71/1.14  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.14  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.14  tff(c_6, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.14  tff(c_16, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.14  tff(c_60, plain, (![B_21, A_22]: (k3_xboole_0(k2_relat_1(B_21), A_22)=k2_relat_1(k8_relat_1(A_22, B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.14  tff(c_69, plain, (![A_22, A_13]: (k2_relat_1(k8_relat_1(A_22, k6_relat_1(A_13)))=k3_xboole_0(A_13, A_22) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_60])).
% 1.71/1.14  tff(c_73, plain, (![A_22, A_13]: (k2_relat_1(k8_relat_1(A_22, k6_relat_1(A_13)))=k3_xboole_0(A_13, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 1.71/1.14  tff(c_74, plain, (![A_23, B_24]: (k2_relat_1(k8_relat_1(A_23, B_24))=A_23 | ~r1_tarski(A_23, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.14  tff(c_77, plain, (![A_23, A_13]: (k2_relat_1(k8_relat_1(A_23, k6_relat_1(A_13)))=A_23 | ~r1_tarski(A_23, A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_74])).
% 1.71/1.14  tff(c_79, plain, (![A_23, A_13]: (k2_relat_1(k8_relat_1(A_23, k6_relat_1(A_13)))=A_23 | ~r1_tarski(A_23, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 1.71/1.14  tff(c_96, plain, (![A_27, A_28]: (k3_xboole_0(A_27, A_28)=A_28 | ~r1_tarski(A_28, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_79])).
% 1.71/1.14  tff(c_100, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_96])).
% 1.71/1.14  tff(c_105, plain, (![A_29, B_30, C_31]: (k8_relat_1(k3_xboole_0(A_29, B_30), C_31)=k8_relat_1(A_29, k8_relat_1(B_30, C_31)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.14  tff(c_126, plain, (![C_32]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', C_32))=k8_relat_1('#skF_1', C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_100, c_105])).
% 1.71/1.14  tff(c_18, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.14  tff(c_132, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_18])).
% 1.71/1.14  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_132])).
% 1.71/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  Inference rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Ref     : 0
% 1.71/1.14  #Sup     : 27
% 1.71/1.14  #Fact    : 0
% 1.71/1.14  #Define  : 0
% 1.71/1.14  #Split   : 0
% 1.71/1.14  #Chain   : 0
% 1.71/1.14  #Close   : 0
% 1.71/1.14  
% 1.71/1.14  Ordering : KBO
% 1.71/1.14  
% 1.71/1.14  Simplification rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Subsume      : 0
% 1.71/1.14  #Demod        : 5
% 1.71/1.14  #Tautology    : 17
% 1.71/1.14  #SimpNegUnit  : 0
% 1.71/1.14  #BackRed      : 0
% 1.71/1.14  
% 1.71/1.14  #Partial instantiations: 0
% 1.71/1.14  #Strategies tried      : 1
% 1.71/1.14  
% 1.71/1.14  Timing (in seconds)
% 1.71/1.14  ----------------------
% 1.71/1.14  Preprocessing        : 0.28
% 1.71/1.14  Parsing              : 0.15
% 1.71/1.14  CNF conversion       : 0.02
% 1.71/1.14  Main loop            : 0.11
% 1.71/1.14  Inferencing          : 0.05
% 1.71/1.14  Reduction            : 0.03
% 1.71/1.14  Demodulation         : 0.03
% 1.71/1.14  BG Simplification    : 0.01
% 1.71/1.14  Subsumption          : 0.01
% 1.71/1.14  Abstraction          : 0.01
% 1.71/1.14  MUC search           : 0.00
% 1.71/1.14  Cooper               : 0.00
% 1.71/1.14  Total                : 0.42
% 1.71/1.14  Index Insertion      : 0.00
% 1.71/1.14  Index Deletion       : 0.00
% 1.71/1.14  Index Matching       : 0.00
% 1.71/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
