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
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_84,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_236,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k4_xboole_0(A_34,B_35),C_36) = k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_273,plain,(
    ! [A_4,C_36] : k4_xboole_0(A_4,k2_xboole_0(A_4,C_36)) = k4_xboole_0(k1_xboole_0,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_236])).

tff(c_305,plain,(
    ! [C_36] : k4_xboole_0(k1_xboole_0,C_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_134,plain,(
    ! [A_29,B_30,C_31] : k4_xboole_0(k3_xboole_0(A_29,B_30),C_31) = k3_xboole_0(A_29,k4_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_31)) = k4_xboole_0(k1_xboole_0,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_134])).

tff(c_399,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_31)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_176])).

tff(c_53,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_18])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.25  
% 2.06/1.25  %Foreground sorts:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Background operators:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Foreground operators:
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.25  
% 2.06/1.26  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.06/1.26  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.06/1.26  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.06/1.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.06/1.26  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.06/1.26  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.06/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.06/1.26  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.06/1.26  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.26  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.26  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.26  tff(c_62, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.26  tff(c_80, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 2.06/1.26  tff(c_84, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80])).
% 2.06/1.26  tff(c_236, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k4_xboole_0(A_34, B_35), C_36)=k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.26  tff(c_273, plain, (![A_4, C_36]: (k4_xboole_0(A_4, k2_xboole_0(A_4, C_36))=k4_xboole_0(k1_xboole_0, C_36))), inference(superposition, [status(thm), theory('equality')], [c_84, c_236])).
% 2.06/1.26  tff(c_305, plain, (![C_36]: (k4_xboole_0(k1_xboole_0, C_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_273])).
% 2.06/1.26  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.26  tff(c_44, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.26  tff(c_48, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_44])).
% 2.06/1.26  tff(c_134, plain, (![A_29, B_30, C_31]: (k4_xboole_0(k3_xboole_0(A_29, B_30), C_31)=k3_xboole_0(A_29, k4_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.26  tff(c_176, plain, (![C_31]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_31))=k4_xboole_0(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_48, c_134])).
% 2.06/1.26  tff(c_399, plain, (![C_31]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_31))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_305, c_176])).
% 2.06/1.26  tff(c_53, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.26  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.26  tff(c_61, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_18])).
% 2.06/1.26  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_61])).
% 2.06/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  Inference rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Ref     : 0
% 2.06/1.26  #Sup     : 91
% 2.06/1.26  #Fact    : 0
% 2.06/1.26  #Define  : 0
% 2.06/1.26  #Split   : 0
% 2.06/1.26  #Chain   : 0
% 2.06/1.26  #Close   : 0
% 2.06/1.26  
% 2.06/1.26  Ordering : KBO
% 2.06/1.26  
% 2.06/1.26  Simplification rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Subsume      : 0
% 2.06/1.26  #Demod        : 36
% 2.06/1.26  #Tautology    : 55
% 2.06/1.26  #SimpNegUnit  : 0
% 2.06/1.26  #BackRed      : 2
% 2.06/1.26  
% 2.06/1.26  #Partial instantiations: 0
% 2.06/1.26  #Strategies tried      : 1
% 2.06/1.26  
% 2.06/1.26  Timing (in seconds)
% 2.06/1.26  ----------------------
% 2.06/1.26  Preprocessing        : 0.29
% 2.06/1.26  Parsing              : 0.16
% 2.06/1.26  CNF conversion       : 0.02
% 2.06/1.26  Main loop            : 0.19
% 2.06/1.26  Inferencing          : 0.07
% 2.06/1.26  Reduction            : 0.07
% 2.06/1.26  Demodulation         : 0.05
% 2.06/1.27  BG Simplification    : 0.01
% 2.06/1.27  Subsumption          : 0.03
% 2.06/1.27  Abstraction          : 0.01
% 2.06/1.27  MUC search           : 0.00
% 2.06/1.27  Cooper               : 0.00
% 2.06/1.27  Total                : 0.50
% 2.06/1.27  Index Insertion      : 0.00
% 2.06/1.27  Index Deletion       : 0.00
% 2.06/1.27  Index Matching       : 0.00
% 2.06/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
