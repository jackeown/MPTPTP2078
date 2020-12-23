%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:40 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  52 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k3_xboole_0(A_35,B_36),k3_xboole_0(A_35,C_37)) = k3_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [A_3,C_37] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_37)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_187,plain,(
    ! [A_38,C_39] : k3_xboole_0(A_38,k2_xboole_0(A_38,C_39)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_176])).

tff(c_223,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_187])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k2_wellord1(k2_wellord1(C_16,A_14),B_15) = k2_wellord1(C_16,k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1100,plain,(
    ! [C_63,B_64,A_65] :
      ( k2_wellord1(k2_wellord1(C_63,B_64),A_65) = k2_wellord1(k2_wellord1(C_63,A_65),B_64)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1139,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_18])).

tff(c_1184,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1139])).

tff(c_1193,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1184])).

tff(c_1196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_223,c_1193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.37  
% 2.75/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.37  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.37  
% 2.75/1.37  %Foreground sorts:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Background operators:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Foreground operators:
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.37  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.75/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.37  
% 2.75/1.38  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 2.75/1.38  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.75/1.38  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.75/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.75/1.38  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.75/1.38  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.75/1.38  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 2.75/1.38  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 2.75/1.38  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.38  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.38  tff(c_79, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.38  tff(c_91, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_79])).
% 2.75/1.38  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.38  tff(c_105, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), A_31)=A_31)), inference(resolution, [status(thm)], [c_8, c_79])).
% 2.75/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.38  tff(c_111, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k3_xboole_0(A_31, B_32))=A_31)), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 2.75/1.38  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.38  tff(c_147, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k3_xboole_0(A_35, C_37))=k3_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.38  tff(c_176, plain, (![A_3, C_37]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_37))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_37)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_147])).
% 2.75/1.38  tff(c_187, plain, (![A_38, C_39]: (k3_xboole_0(A_38, k2_xboole_0(A_38, C_39))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_176])).
% 2.75/1.38  tff(c_223, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_91, c_187])).
% 2.75/1.38  tff(c_14, plain, (![C_16, A_14, B_15]: (k2_wellord1(k2_wellord1(C_16, A_14), B_15)=k2_wellord1(C_16, k3_xboole_0(A_14, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.38  tff(c_1100, plain, (![C_63, B_64, A_65]: (k2_wellord1(k2_wellord1(C_63, B_64), A_65)=k2_wellord1(k2_wellord1(C_63, A_65), B_64) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.38  tff(c_18, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.38  tff(c_1139, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1100, c_18])).
% 2.75/1.38  tff(c_1184, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1139])).
% 2.75/1.38  tff(c_1193, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1184])).
% 2.75/1.38  tff(c_1196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_223, c_1193])).
% 2.75/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  Inference rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Ref     : 0
% 2.75/1.38  #Sup     : 283
% 2.75/1.38  #Fact    : 0
% 2.75/1.38  #Define  : 0
% 2.75/1.38  #Split   : 0
% 2.75/1.38  #Chain   : 0
% 2.75/1.38  #Close   : 0
% 2.75/1.38  
% 2.75/1.38  Ordering : KBO
% 2.75/1.38  
% 2.75/1.38  Simplification rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Subsume      : 0
% 2.75/1.38  #Demod        : 157
% 2.75/1.38  #Tautology    : 204
% 2.75/1.38  #SimpNegUnit  : 0
% 2.75/1.38  #BackRed      : 0
% 2.75/1.38  
% 2.75/1.38  #Partial instantiations: 0
% 2.75/1.38  #Strategies tried      : 1
% 2.75/1.38  
% 2.75/1.38  Timing (in seconds)
% 2.75/1.38  ----------------------
% 2.75/1.38  Preprocessing        : 0.28
% 2.75/1.38  Parsing              : 0.16
% 2.75/1.39  CNF conversion       : 0.02
% 2.75/1.39  Main loop            : 0.35
% 2.75/1.39  Inferencing          : 0.14
% 2.75/1.39  Reduction            : 0.13
% 2.75/1.39  Demodulation         : 0.10
% 2.75/1.39  BG Simplification    : 0.02
% 2.75/1.39  Subsumption          : 0.05
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.66
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
