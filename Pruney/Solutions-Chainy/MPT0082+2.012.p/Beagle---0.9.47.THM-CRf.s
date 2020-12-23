%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  35 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_38,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_16])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_109,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = k3_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_126,plain,(
    ! [A_21] : k3_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_14,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_70,plain,(
    ! [A_18,B_19,C_20] : k3_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k3_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_70])).

tff(c_160,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_95])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.33  
% 2.02/1.33  %Foreground sorts:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Background operators:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Foreground operators:
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.33  
% 2.02/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.02/1.34  tff(f_44, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.02/1.34  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.34  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.02/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.34  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.02/1.34  tff(c_38, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.34  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.34  tff(c_46, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_16])).
% 2.02/1.34  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.34  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.34  tff(c_51, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.34  tff(c_66, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_51])).
% 2.02/1.34  tff(c_109, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_66])).
% 2.02/1.34  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.34  tff(c_114, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=k3_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 2.02/1.34  tff(c_126, plain, (![A_21]: (k3_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114])).
% 2.02/1.34  tff(c_14, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.34  tff(c_33, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.34  tff(c_37, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_33])).
% 2.02/1.34  tff(c_70, plain, (![A_18, B_19, C_20]: (k3_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.34  tff(c_95, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_70])).
% 2.02/1.34  tff(c_160, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_95])).
% 2.02/1.34  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_160])).
% 2.02/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  Inference rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Ref     : 0
% 2.02/1.34  #Sup     : 36
% 2.02/1.34  #Fact    : 0
% 2.02/1.34  #Define  : 0
% 2.02/1.34  #Split   : 0
% 2.02/1.34  #Chain   : 0
% 2.02/1.34  #Close   : 0
% 2.02/1.34  
% 2.02/1.34  Ordering : KBO
% 2.02/1.34  
% 2.02/1.34  Simplification rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Subsume      : 0
% 2.02/1.34  #Demod        : 13
% 2.02/1.34  #Tautology    : 23
% 2.02/1.34  #SimpNegUnit  : 1
% 2.02/1.34  #BackRed      : 0
% 2.02/1.34  
% 2.02/1.34  #Partial instantiations: 0
% 2.02/1.34  #Strategies tried      : 1
% 2.02/1.34  
% 2.02/1.34  Timing (in seconds)
% 2.02/1.34  ----------------------
% 2.02/1.35  Preprocessing        : 0.32
% 2.02/1.35  Parsing              : 0.17
% 2.02/1.35  CNF conversion       : 0.02
% 2.02/1.35  Main loop            : 0.14
% 2.02/1.35  Inferencing          : 0.06
% 2.02/1.35  Reduction            : 0.04
% 2.02/1.35  Demodulation         : 0.03
% 2.02/1.35  BG Simplification    : 0.01
% 2.02/1.35  Subsumption          : 0.02
% 2.02/1.35  Abstraction          : 0.01
% 2.02/1.35  MUC search           : 0.00
% 2.02/1.35  Cooper               : 0.00
% 2.02/1.35  Total                : 0.49
% 2.02/1.35  Index Insertion      : 0.00
% 2.02/1.35  Index Deletion       : 0.00
% 2.02/1.35  Index Matching       : 0.00
% 2.02/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
