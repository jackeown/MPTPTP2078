%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  81 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_14,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_292,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k1_tarski(A_53),k2_tarski(B_54,C_55)) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    ! [B_34,A_35] :
      ( ~ v1_xboole_0(k2_xboole_0(B_34,A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_131,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_35,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_38])).

tff(c_22,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_143,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_22])).

tff(c_327,plain,(
    ! [A_56,B_57,C_58] : k1_enumset1(A_56,B_57,C_58) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_143])).

tff(c_329,plain,(
    ! [A_11,B_12] : k2_tarski(A_11,B_12) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_49,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_115])).

tff(c_129,plain,(
    v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_153,plain,(
    ! [A_36] :
      ( A_36 = '#skF_3'
      | ~ v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_38])).

tff(c_160,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_129,c_153])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.26  
% 1.87/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.26  %$ v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.26  
% 1.87/1.26  %Foreground sorts:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Background operators:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Foreground operators:
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.26  
% 2.06/1.27  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.27  tff(f_44, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.06/1.27  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.27  tff(f_61, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.06/1.27  tff(f_34, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.06/1.27  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.06/1.27  tff(f_57, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.27  tff(c_14, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.27  tff(c_292, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k1_tarski(A_53), k2_tarski(B_54, C_55))=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.27  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.06/1.27  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.27  tff(c_115, plain, (![B_34, A_35]: (~v1_xboole_0(k2_xboole_0(B_34, A_35)) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.27  tff(c_127, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_115])).
% 2.06/1.27  tff(c_131, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 2.06/1.27  tff(c_35, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.27  tff(c_38, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_4, c_35])).
% 2.06/1.27  tff(c_137, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_131, c_38])).
% 2.06/1.27  tff(c_22, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.27  tff(c_143, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_22])).
% 2.06/1.27  tff(c_327, plain, (![A_56, B_57, C_58]: (k1_enumset1(A_56, B_57, C_58)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_292, c_143])).
% 2.06/1.27  tff(c_329, plain, (![A_11, B_12]: (k2_tarski(A_11, B_12)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_327])).
% 2.06/1.27  tff(c_49, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.27  tff(c_67, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_49, c_24])).
% 2.06/1.27  tff(c_118, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_115])).
% 2.06/1.27  tff(c_129, plain, (v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_118])).
% 2.06/1.27  tff(c_153, plain, (![A_36]: (A_36='#skF_3' | ~v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_38])).
% 2.06/1.27  tff(c_160, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_129, c_153])).
% 2.06/1.27  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_160])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 80
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.27  #Split   : 1
% 2.06/1.27  #Chain   : 0
% 2.06/1.27  #Close   : 0
% 2.06/1.27  
% 2.06/1.27  Ordering : KBO
% 2.06/1.27  
% 2.06/1.27  Simplification rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Subsume      : 18
% 2.06/1.27  #Demod        : 28
% 2.06/1.27  #Tautology    : 42
% 2.06/1.27  #SimpNegUnit  : 1
% 2.06/1.27  #BackRed      : 8
% 2.06/1.27  
% 2.06/1.27  #Partial instantiations: 0
% 2.06/1.27  #Strategies tried      : 1
% 2.06/1.27  
% 2.06/1.27  Timing (in seconds)
% 2.06/1.27  ----------------------
% 2.06/1.27  Preprocessing        : 0.27
% 2.06/1.27  Parsing              : 0.14
% 2.06/1.27  CNF conversion       : 0.01
% 2.06/1.27  Main loop            : 0.19
% 2.06/1.27  Inferencing          : 0.06
% 2.06/1.27  Reduction            : 0.07
% 2.06/1.27  Demodulation         : 0.05
% 2.06/1.27  BG Simplification    : 0.01
% 2.06/1.27  Subsumption          : 0.03
% 2.06/1.27  Abstraction          : 0.01
% 2.06/1.27  MUC search           : 0.00
% 2.06/1.27  Cooper               : 0.00
% 2.06/1.27  Total                : 0.48
% 2.06/1.27  Index Insertion      : 0.00
% 2.06/1.27  Index Deletion       : 0.00
% 2.06/1.27  Index Matching       : 0.00
% 2.06/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
