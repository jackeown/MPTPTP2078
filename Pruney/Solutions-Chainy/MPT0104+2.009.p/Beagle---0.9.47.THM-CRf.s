%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  46 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_33,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_18])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_23,B_24] : k4_xboole_0(k2_xboole_0(A_23,B_24),B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k2_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8])).

tff(c_129,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_120])).

tff(c_20,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_38])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) = k5_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_22,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_322,plain,(
    ! [A_33,C_34,B_35] : k2_xboole_0(k4_xboole_0(A_33,C_34),k4_xboole_0(B_35,C_34)) = k4_xboole_0(k2_xboole_0(A_33,B_35),C_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_765,plain,(
    ! [B_45] : k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_45),'#skF_3') = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_45,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_322])).

tff(c_810,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3')) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_765])).

tff(c_824,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_49,c_810])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.41  
% 2.54/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.41  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.41  
% 2.54/1.41  %Foreground sorts:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Background operators:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Foreground operators:
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.41  
% 2.54/1.42  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.54/1.42  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 2.54/1.42  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.54/1.42  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.54/1.42  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.54/1.42  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 2.54/1.42  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.54/1.42  tff(c_33, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.42  tff(c_18, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.42  tff(c_37, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_18])).
% 2.54/1.42  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.42  tff(c_110, plain, (![A_23, B_24]: (k4_xboole_0(k2_xboole_0(A_23, B_24), B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.42  tff(c_120, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k2_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_8])).
% 2.54/1.42  tff(c_129, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_120])).
% 2.54/1.42  tff(c_20, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.42  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.42  tff(c_49, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_38])).
% 2.54/1.42  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.42  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.42  tff(c_23, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13))=k5_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.54/1.42  tff(c_22, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.42  tff(c_50, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_38])).
% 2.54/1.42  tff(c_322, plain, (![A_33, C_34, B_35]: (k2_xboole_0(k4_xboole_0(A_33, C_34), k4_xboole_0(B_35, C_34))=k4_xboole_0(k2_xboole_0(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.42  tff(c_765, plain, (![B_45]: (k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_45), '#skF_3')=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_45, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_322])).
% 2.54/1.42  tff(c_810, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3'))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23, c_765])).
% 2.54/1.42  tff(c_824, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_49, c_810])).
% 2.54/1.42  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_824])).
% 2.54/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.42  
% 2.54/1.42  Inference rules
% 2.54/1.42  ----------------------
% 2.54/1.42  #Ref     : 0
% 2.54/1.42  #Sup     : 216
% 2.54/1.42  #Fact    : 0
% 2.54/1.42  #Define  : 0
% 2.54/1.42  #Split   : 0
% 2.54/1.42  #Chain   : 0
% 2.54/1.42  #Close   : 0
% 2.54/1.42  
% 2.54/1.42  Ordering : KBO
% 2.54/1.42  
% 2.54/1.42  Simplification rules
% 2.54/1.42  ----------------------
% 2.54/1.42  #Subsume      : 3
% 2.54/1.42  #Demod        : 122
% 2.54/1.42  #Tautology    : 102
% 2.54/1.42  #SimpNegUnit  : 1
% 2.54/1.42  #BackRed      : 0
% 2.54/1.42  
% 2.54/1.42  #Partial instantiations: 0
% 2.54/1.42  #Strategies tried      : 1
% 2.54/1.42  
% 2.54/1.42  Timing (in seconds)
% 2.54/1.42  ----------------------
% 2.54/1.43  Preprocessing        : 0.29
% 2.54/1.43  Parsing              : 0.16
% 2.54/1.43  CNF conversion       : 0.02
% 2.54/1.43  Main loop            : 0.34
% 2.54/1.43  Inferencing          : 0.12
% 2.54/1.43  Reduction            : 0.12
% 2.54/1.43  Demodulation         : 0.10
% 2.54/1.43  BG Simplification    : 0.02
% 2.54/1.43  Subsumption          : 0.05
% 2.54/1.43  Abstraction          : 0.02
% 2.54/1.43  MUC search           : 0.00
% 2.54/1.43  Cooper               : 0.00
% 2.54/1.43  Total                : 0.65
% 2.54/1.43  Index Insertion      : 0.00
% 2.54/1.43  Index Deletion       : 0.00
% 2.54/1.43  Index Matching       : 0.00
% 2.54/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
