%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  46 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_6,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_21,k1_xboole_0)) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_33,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_4])).

tff(c_156,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_49])).

tff(c_167,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_49])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_185,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_197,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k3_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_8])).

tff(c_206,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_197])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_209,plain,(
    ! [C_24,A_25,B_26] :
      ( k2_wellord1(k2_wellord1(C_24,A_25),B_26) = k2_wellord1(C_24,k3_xboole_0(A_25,B_26))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    k2_wellord1(k2_wellord1('#skF_2','#skF_1'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_218,plain,
    ( k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_14])).

tff(c_227,plain,(
    k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_218])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.16  %$ v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.16  
% 1.89/1.16  %Foreground sorts:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Background operators:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Foreground operators:
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.89/1.16  
% 1.89/1.17  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.89/1.17  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.89/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.89/1.17  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.89/1.17  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.89/1.17  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 1.89/1.17  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 1.89/1.17  tff(c_6, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.17  tff(c_135, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.17  tff(c_150, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_21, k1_xboole_0))=A_21)), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 1.89/1.17  tff(c_33, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.17  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.17  tff(c_49, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_33, c_4])).
% 1.89/1.17  tff(c_156, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_150, c_49])).
% 1.89/1.17  tff(c_167, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_150, c_49])).
% 1.89/1.17  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.17  tff(c_176, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 1.89/1.17  tff(c_185, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_176])).
% 1.89/1.17  tff(c_197, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k3_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_185, c_8])).
% 1.89/1.17  tff(c_206, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_197])).
% 1.89/1.17  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.17  tff(c_209, plain, (![C_24, A_25, B_26]: (k2_wellord1(k2_wellord1(C_24, A_25), B_26)=k2_wellord1(C_24, k3_xboole_0(A_25, B_26)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.17  tff(c_14, plain, (k2_wellord1(k2_wellord1('#skF_2', '#skF_1'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.17  tff(c_218, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209, c_14])).
% 1.89/1.17  tff(c_227, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_218])).
% 1.89/1.17  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_227])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 56
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 0
% 1.89/1.17  #Demod        : 20
% 1.89/1.17  #Tautology    : 46
% 1.89/1.17  #SimpNegUnit  : 0
% 1.89/1.17  #BackRed      : 1
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.18  Preprocessing        : 0.26
% 1.89/1.18  Parsing              : 0.14
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.15
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.06
% 1.89/1.18  Demodulation         : 0.05
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.02
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.44
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
