%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_165,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k4_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_200,plain,(
    ! [C_27] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_27)) = k4_xboole_0(k1_xboole_0,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_165])).

tff(c_216,plain,(
    ! [C_27] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_27)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_200])).

tff(c_54,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_18])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n024.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.26  
% 1.97/1.26  %Foreground sorts:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Background operators:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Foreground operators:
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.26  
% 1.97/1.27  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.97/1.27  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.97/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.97/1.27  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.97/1.27  tff(c_16, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.27  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.27  tff(c_59, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.27  tff(c_67, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_59])).
% 1.97/1.27  tff(c_165, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k4_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.27  tff(c_200, plain, (![C_27]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_27))=k4_xboole_0(k1_xboole_0, C_27))), inference(superposition, [status(thm), theory('equality')], [c_67, c_165])).
% 1.97/1.27  tff(c_216, plain, (![C_27]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_27))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_200])).
% 1.97/1.27  tff(c_54, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.27  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.27  tff(c_58, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_18])).
% 1.97/1.27  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_58])).
% 1.97/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  Inference rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Ref     : 0
% 1.97/1.27  #Sup     : 65
% 1.97/1.27  #Fact    : 0
% 1.97/1.27  #Define  : 0
% 1.97/1.27  #Split   : 0
% 1.97/1.27  #Chain   : 0
% 1.97/1.27  #Close   : 0
% 1.97/1.27  
% 1.97/1.27  Ordering : KBO
% 1.97/1.27  
% 1.97/1.27  Simplification rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Subsume      : 0
% 1.97/1.27  #Demod        : 32
% 1.97/1.27  #Tautology    : 47
% 1.97/1.27  #SimpNegUnit  : 0
% 1.97/1.27  #BackRed      : 1
% 1.97/1.27  
% 1.97/1.27  #Partial instantiations: 0
% 1.97/1.27  #Strategies tried      : 1
% 1.97/1.27  
% 1.97/1.27  Timing (in seconds)
% 1.97/1.27  ----------------------
% 1.97/1.27  Preprocessing        : 0.33
% 1.97/1.27  Parsing              : 0.15
% 1.97/1.27  CNF conversion       : 0.03
% 1.97/1.27  Main loop            : 0.19
% 1.97/1.27  Inferencing          : 0.07
% 1.97/1.27  Reduction            : 0.07
% 1.97/1.27  Demodulation         : 0.05
% 1.97/1.27  BG Simplification    : 0.02
% 1.97/1.27  Subsumption          : 0.02
% 1.97/1.27  Abstraction          : 0.01
% 1.97/1.27  MUC search           : 0.00
% 1.97/1.27  Cooper               : 0.00
% 1.97/1.27  Total                : 0.54
% 1.97/1.27  Index Insertion      : 0.00
% 1.97/1.27  Index Deletion       : 0.00
% 1.97/1.27  Index Matching       : 0.00
% 1.97/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
