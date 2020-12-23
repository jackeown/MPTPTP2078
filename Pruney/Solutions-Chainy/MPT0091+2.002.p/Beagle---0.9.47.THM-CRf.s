%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  35 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_141,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_18])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_153,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),k3_xboole_0(A_20,C_22)) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_183,plain,(
    ! [B_21] : k4_xboole_0(k3_xboole_0('#skF_1',B_21),k1_xboole_0) = k3_xboole_0('#skF_1',k4_xboole_0(B_21,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_153])).

tff(c_215,plain,(
    ! [B_25] : k3_xboole_0('#skF_1',k4_xboole_0(B_25,'#skF_3')) = k3_xboole_0('#skF_1',B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_227,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_91])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.20  
% 1.89/1.21  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.89/1.21  tff(f_48, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 1.89/1.21  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.89/1.21  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 1.89/1.21  tff(c_141, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.21  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.21  tff(c_152, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_18])).
% 1.89/1.21  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.21  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.21  tff(c_76, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.21  tff(c_92, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_76])).
% 1.89/1.21  tff(c_153, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), k3_xboole_0(A_20, C_22))=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.21  tff(c_183, plain, (![B_21]: (k4_xboole_0(k3_xboole_0('#skF_1', B_21), k1_xboole_0)=k3_xboole_0('#skF_1', k4_xboole_0(B_21, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_153])).
% 1.89/1.21  tff(c_215, plain, (![B_25]: (k3_xboole_0('#skF_1', k4_xboole_0(B_25, '#skF_3'))=k3_xboole_0('#skF_1', B_25))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_183])).
% 1.89/1.21  tff(c_14, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.21  tff(c_91, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_76])).
% 1.89/1.21  tff(c_227, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_215, c_91])).
% 1.89/1.21  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_227])).
% 1.89/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  Inference rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Ref     : 0
% 1.89/1.21  #Sup     : 60
% 1.89/1.21  #Fact    : 0
% 1.89/1.21  #Define  : 0
% 1.89/1.21  #Split   : 0
% 1.89/1.21  #Chain   : 0
% 1.89/1.21  #Close   : 0
% 1.89/1.21  
% 1.89/1.21  Ordering : KBO
% 1.89/1.21  
% 1.89/1.21  Simplification rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Subsume      : 2
% 1.89/1.21  #Demod        : 17
% 1.89/1.21  #Tautology    : 32
% 1.89/1.21  #SimpNegUnit  : 1
% 1.89/1.21  #BackRed      : 0
% 1.89/1.21  
% 1.89/1.21  #Partial instantiations: 0
% 1.89/1.21  #Strategies tried      : 1
% 1.89/1.21  
% 1.89/1.21  Timing (in seconds)
% 1.89/1.21  ----------------------
% 1.89/1.21  Preprocessing        : 0.28
% 1.89/1.21  Parsing              : 0.15
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.18
% 1.89/1.21  Inferencing          : 0.07
% 1.89/1.21  Reduction            : 0.06
% 1.89/1.21  Demodulation         : 0.05
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.03
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.48
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
