%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  39 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_24,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_29] : k5_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_21,B_22] : k3_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_354,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_376,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = k5_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_354])).

tff(c_391,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_376])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_278,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_290,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_278])).

tff(c_373,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_354])).

tff(c_531,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_373])).

tff(c_30,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_535,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_30])).

tff(c_541,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_535])).

tff(c_630,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,k2_xboole_0(C_66,B_67))
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1113,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,'#skF_4')
      | ~ r1_tarski(A_88,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_630])).

tff(c_1130,plain,(
    ! [B_26] : r1_tarski(k4_xboole_0('#skF_3',B_26),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1113])).

tff(c_32,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.38  
% 2.75/1.39  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.75/1.39  tff(f_73, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.75/1.39  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.75/1.39  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.75/1.39  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.75/1.39  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.75/1.39  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.75/1.39  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.75/1.39  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.75/1.39  tff(c_24, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.75/1.39  tff(c_28, plain, (![A_29]: (k5_xboole_0(A_29, k1_xboole_0)=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.75/1.39  tff(c_26, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.39  tff(c_20, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k2_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.39  tff(c_354, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.39  tff(c_376, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k2_xboole_0(A_21, B_22))=k5_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_354])).
% 2.75/1.39  tff(c_391, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_376])).
% 2.75/1.39  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.39  tff(c_278, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.39  tff(c_290, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_278])).
% 2.75/1.39  tff(c_373, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_290, c_354])).
% 2.75/1.39  tff(c_531, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_391, c_373])).
% 2.75/1.39  tff(c_30, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.39  tff(c_535, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_531, c_30])).
% 2.75/1.39  tff(c_541, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_535])).
% 2.75/1.39  tff(c_630, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, k2_xboole_0(C_66, B_67)) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.39  tff(c_1113, plain, (![A_88]: (r1_tarski(A_88, '#skF_4') | ~r1_tarski(A_88, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_541, c_630])).
% 2.75/1.39  tff(c_1130, plain, (![B_26]: (r1_tarski(k4_xboole_0('#skF_3', B_26), '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1113])).
% 2.75/1.39  tff(c_32, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.39  tff(c_1134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1130, c_32])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 265
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 2
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 1
% 2.75/1.39  #Demod        : 136
% 2.75/1.39  #Tautology    : 203
% 2.75/1.39  #SimpNegUnit  : 4
% 2.75/1.39  #BackRed      : 4
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.40  Preprocessing        : 0.28
% 2.75/1.40  Parsing              : 0.16
% 2.75/1.40  CNF conversion       : 0.02
% 2.75/1.40  Main loop            : 0.36
% 2.75/1.40  Inferencing          : 0.13
% 2.75/1.40  Reduction            : 0.13
% 2.75/1.40  Demodulation         : 0.10
% 2.75/1.40  BG Simplification    : 0.02
% 2.75/1.40  Subsumption          : 0.05
% 2.75/1.40  Abstraction          : 0.01
% 2.75/1.40  MUC search           : 0.00
% 2.75/1.40  Cooper               : 0.00
% 2.75/1.40  Total                : 0.67
% 2.75/1.40  Index Insertion      : 0.00
% 2.75/1.40  Index Deletion       : 0.00
% 2.75/1.40  Index Matching       : 0.00
% 2.75/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
