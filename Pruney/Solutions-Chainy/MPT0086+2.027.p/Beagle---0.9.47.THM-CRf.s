%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  40 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(B_19,A_20)
      | ~ r1_xboole_0(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_12] : r1_xboole_0(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_14,c_45])).

tff(c_128,plain,(
    ! [A_28,B_29,C_30] : k4_xboole_0(k4_xboole_0(A_28,B_29),C_30) = k4_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_72,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_138,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k2_xboole_0(B_29,k4_xboole_0(A_28,B_29))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_72])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_28,B_29,B_11] : k4_xboole_0(A_28,k2_xboole_0(B_29,k4_xboole_0(k4_xboole_0(A_28,B_29),B_11))) = k3_xboole_0(k4_xboole_0(A_28,B_29),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_12])).

tff(c_2670,plain,(
    ! [A_89,B_90,B_91] : k4_xboole_0(A_89,k2_xboole_0(B_90,k4_xboole_0(A_89,k2_xboole_0(B_90,B_91)))) = k3_xboole_0(k4_xboole_0(A_89,B_90),B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_2850,plain,(
    ! [A_89,A_1] : k4_xboole_0(A_89,k2_xboole_0(A_1,k4_xboole_0(A_89,A_1))) = k3_xboole_0(k4_xboole_0(A_89,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2670])).

tff(c_2893,plain,(
    ! [A_92,A_93] : k3_xboole_0(k4_xboole_0(A_92,A_93),A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2850])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( ~ r1_xboole_0(k3_xboole_0(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2912,plain,(
    ! [A_93,A_92] :
      ( ~ r1_xboole_0(k1_xboole_0,A_93)
      | r1_xboole_0(k4_xboole_0(A_92,A_93),A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2893,c_16])).

tff(c_3013,plain,(
    ! [A_92,A_93] : r1_xboole_0(k4_xboole_0(A_92,A_93),A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2912])).

tff(c_18,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3013,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.66  
% 3.78/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.66  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.78/1.66  
% 3.78/1.66  %Foreground sorts:
% 3.78/1.66  
% 3.78/1.66  
% 3.78/1.66  %Background operators:
% 3.78/1.66  
% 3.78/1.66  
% 3.78/1.66  %Foreground operators:
% 3.78/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.78/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.78/1.66  
% 3.78/1.67  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.78/1.67  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.78/1.67  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.78/1.67  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.78/1.67  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.78/1.67  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.78/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.78/1.67  tff(f_47, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.78/1.67  tff(f_50, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.78/1.67  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.78/1.67  tff(c_45, plain, (![B_19, A_20]: (r1_xboole_0(B_19, A_20) | ~r1_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.67  tff(c_48, plain, (![A_12]: (r1_xboole_0(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_14, c_45])).
% 3.78/1.67  tff(c_128, plain, (![A_28, B_29, C_30]: (k4_xboole_0(k4_xboole_0(A_28, B_29), C_30)=k4_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.67  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.78/1.67  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.67  tff(c_54, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.67  tff(c_69, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_54])).
% 3.78/1.67  tff(c_72, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 3.78/1.67  tff(c_138, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k2_xboole_0(B_29, k4_xboole_0(A_28, B_29)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_72])).
% 3.78/1.67  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.78/1.67  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.67  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.67  tff(c_145, plain, (![A_28, B_29, B_11]: (k4_xboole_0(A_28, k2_xboole_0(B_29, k4_xboole_0(k4_xboole_0(A_28, B_29), B_11)))=k3_xboole_0(k4_xboole_0(A_28, B_29), B_11))), inference(superposition, [status(thm), theory('equality')], [c_128, c_12])).
% 3.78/1.67  tff(c_2670, plain, (![A_89, B_90, B_91]: (k4_xboole_0(A_89, k2_xboole_0(B_90, k4_xboole_0(A_89, k2_xboole_0(B_90, B_91))))=k3_xboole_0(k4_xboole_0(A_89, B_90), B_91))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_145])).
% 3.78/1.67  tff(c_2850, plain, (![A_89, A_1]: (k4_xboole_0(A_89, k2_xboole_0(A_1, k4_xboole_0(A_89, A_1)))=k3_xboole_0(k4_xboole_0(A_89, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2670])).
% 3.78/1.67  tff(c_2893, plain, (![A_92, A_93]: (k3_xboole_0(k4_xboole_0(A_92, A_93), A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2850])).
% 3.78/1.67  tff(c_16, plain, (![A_13, B_14]: (~r1_xboole_0(k3_xboole_0(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.67  tff(c_2912, plain, (![A_93, A_92]: (~r1_xboole_0(k1_xboole_0, A_93) | r1_xboole_0(k4_xboole_0(A_92, A_93), A_93))), inference(superposition, [status(thm), theory('equality')], [c_2893, c_16])).
% 3.78/1.67  tff(c_3013, plain, (![A_92, A_93]: (r1_xboole_0(k4_xboole_0(A_92, A_93), A_93))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2912])).
% 3.78/1.67  tff(c_18, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.78/1.67  tff(c_3039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3013, c_18])).
% 3.78/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.67  
% 3.78/1.67  Inference rules
% 3.78/1.67  ----------------------
% 3.78/1.67  #Ref     : 0
% 3.78/1.67  #Sup     : 727
% 3.78/1.67  #Fact    : 0
% 3.78/1.67  #Define  : 0
% 3.78/1.67  #Split   : 0
% 3.78/1.67  #Chain   : 0
% 3.78/1.67  #Close   : 0
% 3.78/1.67  
% 3.78/1.67  Ordering : KBO
% 3.78/1.67  
% 3.78/1.67  Simplification rules
% 3.78/1.67  ----------------------
% 3.78/1.67  #Subsume      : 1
% 3.78/1.67  #Demod        : 580
% 3.78/1.67  #Tautology    : 462
% 3.78/1.67  #SimpNegUnit  : 0
% 3.78/1.67  #BackRed      : 2
% 3.78/1.67  
% 3.78/1.67  #Partial instantiations: 0
% 3.78/1.67  #Strategies tried      : 1
% 3.78/1.67  
% 3.78/1.67  Timing (in seconds)
% 3.78/1.67  ----------------------
% 3.78/1.67  Preprocessing        : 0.27
% 3.78/1.67  Parsing              : 0.16
% 3.78/1.67  CNF conversion       : 0.01
% 3.78/1.67  Main loop            : 0.59
% 3.78/1.67  Inferencing          : 0.22
% 3.78/1.67  Reduction            : 0.22
% 3.78/1.67  Demodulation         : 0.18
% 3.78/1.67  BG Simplification    : 0.03
% 3.78/1.67  Subsumption          : 0.08
% 3.78/1.67  Abstraction          : 0.04
% 3.78/1.67  MUC search           : 0.00
% 3.78/1.67  Cooper               : 0.00
% 3.78/1.67  Total                : 0.89
% 3.78/1.67  Index Insertion      : 0.00
% 3.78/1.67  Index Deletion       : 0.00
% 3.78/1.67  Index Matching       : 0.00
% 3.78/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
