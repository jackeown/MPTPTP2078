%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:10 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_22,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [B_25,A_26] :
      ( ~ r2_xboole_0(B_25,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_54,plain,(
    ! [B_22,A_23] : k5_xboole_0(B_22,A_23) = k5_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_325,plain,(
    ! [A_38,B_39,C_40] : k5_xboole_0(k5_xboole_0(A_38,B_39),C_40) = k5_xboole_0(A_38,k5_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_417,plain,(
    ! [A_13,C_40] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_40)) = k5_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_325])).

tff(c_435,plain,(
    ! [A_13,C_40] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_40)) = C_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_417])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_183,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_183])).

tff(c_206,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_233,plain,(
    ! [A_33,B_34] : k5_xboole_0(k5_xboole_0(A_33,B_34),k2_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_254,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_233])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_619,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_12])).

tff(c_641,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_2,c_619])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_655,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_6])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:39:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  
% 2.42/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.42/1.36  
% 2.42/1.36  %Foreground sorts:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Background operators:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Foreground operators:
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.36  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.36  
% 2.51/1.37  tff(f_52, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.51/1.37  tff(f_38, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.51/1.37  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.51/1.37  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.51/1.37  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.51/1.37  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.51/1.37  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.51/1.37  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.51/1.37  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.51/1.37  tff(c_22, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.37  tff(c_150, plain, (![B_25, A_26]: (~r2_xboole_0(B_25, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.37  tff(c_154, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_150])).
% 2.51/1.37  tff(c_54, plain, (![B_22, A_23]: (k5_xboole_0(B_22, A_23)=k5_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.37  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.37  tff(c_70, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 2.51/1.37  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.51/1.37  tff(c_325, plain, (![A_38, B_39, C_40]: (k5_xboole_0(k5_xboole_0(A_38, B_39), C_40)=k5_xboole_0(A_38, k5_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.37  tff(c_417, plain, (![A_13, C_40]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_40))=k5_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_14, c_325])).
% 2.51/1.37  tff(c_435, plain, (![A_13, C_40]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_40))=C_40)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_417])).
% 2.51/1.37  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.37  tff(c_20, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.37  tff(c_183, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.37  tff(c_203, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_183])).
% 2.51/1.37  tff(c_206, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 2.51/1.37  tff(c_233, plain, (![A_33, B_34]: (k5_xboole_0(k5_xboole_0(A_33, B_34), k2_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.37  tff(c_254, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_206, c_233])).
% 2.51/1.37  tff(c_12, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.37  tff(c_619, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_254, c_12])).
% 2.51/1.37  tff(c_641, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_2, c_619])).
% 2.51/1.37  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.37  tff(c_655, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_641, c_6])).
% 2.51/1.37  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_655])).
% 2.51/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  Inference rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Ref     : 0
% 2.51/1.37  #Sup     : 165
% 2.51/1.37  #Fact    : 0
% 2.51/1.37  #Define  : 0
% 2.51/1.37  #Split   : 0
% 2.51/1.37  #Chain   : 0
% 2.51/1.37  #Close   : 0
% 2.51/1.37  
% 2.51/1.37  Ordering : KBO
% 2.51/1.37  
% 2.51/1.37  Simplification rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Subsume      : 1
% 2.51/1.37  #Demod        : 55
% 2.51/1.37  #Tautology    : 85
% 2.51/1.37  #SimpNegUnit  : 1
% 2.51/1.37  #BackRed      : 1
% 2.51/1.37  
% 2.51/1.37  #Partial instantiations: 0
% 2.51/1.37  #Strategies tried      : 1
% 2.51/1.37  
% 2.51/1.37  Timing (in seconds)
% 2.51/1.37  ----------------------
% 2.51/1.37  Preprocessing        : 0.28
% 2.51/1.37  Parsing              : 0.16
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.29
% 2.51/1.37  Inferencing          : 0.10
% 2.51/1.37  Reduction            : 0.12
% 2.51/1.37  Demodulation         : 0.10
% 2.51/1.37  BG Simplification    : 0.01
% 2.51/1.37  Subsumption          : 0.04
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.59
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
