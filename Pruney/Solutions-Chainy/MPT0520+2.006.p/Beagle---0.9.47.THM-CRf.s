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
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_18,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(B_26,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [B_26,A_25] : k3_xboole_0(B_26,A_25) = k3_xboole_0(A_25,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_14])).

tff(c_182,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(k2_relat_1(B_31),A_32) = k2_relat_1(k8_relat_1(A_32,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_397,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,k2_relat_1(B_41)) = k2_relat_1(k8_relat_1(A_40,B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_182])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    k4_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_160,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_160])).

tff(c_181,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_410,plain,
    ( k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_181])).

tff(c_441,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_410])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:57:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.25  
% 2.08/1.26  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 2.08/1.26  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.08/1.26  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.08/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.08/1.26  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.08/1.26  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.08/1.26  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.08/1.26  tff(c_18, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.26  tff(c_74, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.26  tff(c_103, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(B_26, A_25))), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 2.08/1.26  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.26  tff(c_109, plain, (![B_26, A_25]: (k3_xboole_0(B_26, A_25)=k3_xboole_0(A_25, B_26))), inference(superposition, [status(thm), theory('equality')], [c_103, c_14])).
% 2.08/1.26  tff(c_182, plain, (![B_31, A_32]: (k3_xboole_0(k2_relat_1(B_31), A_32)=k2_relat_1(k8_relat_1(A_32, B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.26  tff(c_397, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k2_relat_1(B_41))=k2_relat_1(k8_relat_1(A_40, B_41)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_109, c_182])).
% 2.08/1.26  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.26  tff(c_20, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_65, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.26  tff(c_69, plain, (k4_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.08/1.26  tff(c_160, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.26  tff(c_175, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_160])).
% 2.08/1.26  tff(c_181, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 2.08/1.26  tff(c_410, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_397, c_181])).
% 2.08/1.26  tff(c_441, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_410])).
% 2.08/1.26  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_441])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 109
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 0
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 5
% 2.08/1.26  #Demod        : 31
% 2.08/1.26  #Tautology    : 63
% 2.08/1.26  #SimpNegUnit  : 1
% 2.08/1.26  #BackRed      : 0
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.26  Preprocessing        : 0.28
% 2.08/1.26  Parsing              : 0.15
% 2.08/1.26  CNF conversion       : 0.02
% 2.08/1.26  Main loop            : 0.22
% 2.08/1.26  Inferencing          : 0.08
% 2.08/1.26  Reduction            : 0.08
% 2.08/1.26  Demodulation         : 0.06
% 2.08/1.26  BG Simplification    : 0.01
% 2.08/1.26  Subsumption          : 0.03
% 2.08/1.26  Abstraction          : 0.01
% 2.08/1.26  MUC search           : 0.00
% 2.08/1.26  Cooper               : 0.00
% 2.08/1.26  Total                : 0.52
% 2.08/1.26  Index Insertion      : 0.00
% 2.08/1.26  Index Deletion       : 0.00
% 2.08/1.26  Index Matching       : 0.00
% 2.08/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
