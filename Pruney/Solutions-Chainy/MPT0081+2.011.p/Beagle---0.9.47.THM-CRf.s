%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 (  44 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_98,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_161,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_161])).

tff(c_184,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_176])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)) = k4_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_224,plain,(
    ! [C_13] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_13)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_16])).

tff(c_487,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_40)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_499,plain,(
    ! [C_40] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_40)) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_14])).

tff(c_530,plain,(
    ! [C_41] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_499])).

tff(c_557,plain,(
    ! [B_10] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_530])).

tff(c_49,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_20])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.27  
% 1.96/1.27  %Foreground sorts:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Background operators:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Foreground operators:
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.27  
% 2.13/1.28  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.13/1.28  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.13/1.28  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.13/1.28  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.13/1.28  tff(f_48, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.13/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.13/1.28  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.13/1.28  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.13/1.28  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.28  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.28  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.28  tff(c_80, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.28  tff(c_95, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.13/1.28  tff(c_98, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 2.13/1.28  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.28  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.28  tff(c_63, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.28  tff(c_71, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.13/1.28  tff(c_161, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.28  tff(c_176, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_161])).
% 2.13/1.28  tff(c_184, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_176])).
% 2.13/1.28  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13))=k4_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.28  tff(c_224, plain, (![C_13]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_13))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_13)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_16])).
% 2.13/1.28  tff(c_487, plain, (![C_40]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_40))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_224])).
% 2.13/1.28  tff(c_499, plain, (![C_40]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_40))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_14])).
% 2.13/1.28  tff(c_530, plain, (![C_41]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_499])).
% 2.13/1.28  tff(c_557, plain, (![B_10]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_530])).
% 2.13/1.28  tff(c_49, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.28  tff(c_20, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.28  tff(c_53, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_20])).
% 2.13/1.28  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_557, c_53])).
% 2.13/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  Inference rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Ref     : 0
% 2.13/1.28  #Sup     : 137
% 2.13/1.28  #Fact    : 0
% 2.13/1.28  #Define  : 0
% 2.13/1.28  #Split   : 0
% 2.13/1.28  #Chain   : 0
% 2.13/1.28  #Close   : 0
% 2.13/1.28  
% 2.13/1.28  Ordering : KBO
% 2.13/1.28  
% 2.13/1.28  Simplification rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Subsume      : 0
% 2.13/1.28  #Demod        : 99
% 2.13/1.28  #Tautology    : 108
% 2.13/1.28  #SimpNegUnit  : 0
% 2.13/1.28  #BackRed      : 2
% 2.13/1.28  
% 2.13/1.28  #Partial instantiations: 0
% 2.13/1.28  #Strategies tried      : 1
% 2.13/1.28  
% 2.13/1.28  Timing (in seconds)
% 2.13/1.28  ----------------------
% 2.13/1.29  Preprocessing        : 0.25
% 2.13/1.29  Parsing              : 0.14
% 2.13/1.29  CNF conversion       : 0.02
% 2.13/1.29  Main loop            : 0.23
% 2.13/1.29  Inferencing          : 0.10
% 2.13/1.29  Reduction            : 0.08
% 2.13/1.29  Demodulation         : 0.06
% 2.13/1.29  BG Simplification    : 0.01
% 2.13/1.29  Subsumption          : 0.03
% 2.13/1.29  Abstraction          : 0.01
% 2.13/1.29  MUC search           : 0.00
% 2.13/1.29  Cooper               : 0.00
% 2.13/1.29  Total                : 0.51
% 2.13/1.29  Index Insertion      : 0.00
% 2.13/1.29  Index Deletion       : 0.00
% 2.13/1.29  Index Matching       : 0.00
% 2.13/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
