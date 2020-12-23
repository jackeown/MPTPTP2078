%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   42 (  72 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  78 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_168,plain,(
    ! [A_25,B_26,C_27] : k3_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k3_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [C_27] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_27)) = k3_xboole_0('#skF_1',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_168])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_4015,plain,(
    ! [A_101,B_102,B_103] : k3_xboole_0(A_101,k3_xboole_0(B_102,k2_xboole_0(k3_xboole_0(A_101,B_102),B_103))) = k3_xboole_0(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_168])).

tff(c_6568,plain,(
    ! [A_130,B_131] : k3_xboole_0(A_130,k3_xboole_0(B_131,A_130)) = k3_xboole_0(A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4015])).

tff(c_6735,plain,(
    ! [B_131] : k3_xboole_0('#skF_1',k3_xboole_0(B_131,'#skF_2')) = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6568,c_199])).

tff(c_14523,plain,(
    ! [B_179] : k3_xboole_0('#skF_1',k3_xboole_0(B_179,'#skF_2')) = k3_xboole_0('#skF_1',B_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_6735])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_1955,plain,(
    ! [A_70,B_71,C_72] : k3_xboole_0(A_70,k3_xboole_0(k2_xboole_0(A_70,B_71),C_72)) = k3_xboole_0(A_70,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_168])).

tff(c_2234,plain,(
    ! [C_74] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_74)) = k3_xboole_0('#skF_3',C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1955])).

tff(c_19,plain,(
    ! [B_14,A_15] : k3_xboole_0(B_14,A_15) = k3_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [B_14,A_15] : r1_tarski(k3_xboole_0(B_14,A_15),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_8])).

tff(c_181,plain,(
    ! [A_25,B_26,C_27] : r1_tarski(k3_xboole_0(A_25,k3_xboole_0(B_26,C_27)),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_34])).

tff(c_2275,plain,(
    ! [A_25,C_74] : r1_tarski(k3_xboole_0(A_25,k3_xboole_0('#skF_3',C_74)),k3_xboole_0('#skF_4',C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_181])).

tff(c_14570,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14523,c_2275])).

tff(c_14783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_14570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.25/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.01  
% 8.25/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.01  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.25/3.01  
% 8.25/3.01  %Foreground sorts:
% 8.25/3.01  
% 8.25/3.01  
% 8.25/3.01  %Background operators:
% 8.25/3.01  
% 8.25/3.01  
% 8.25/3.01  %Foreground operators:
% 8.25/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.25/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.25/3.01  tff('#skF_2', type, '#skF_2': $i).
% 8.25/3.01  tff('#skF_3', type, '#skF_3': $i).
% 8.25/3.01  tff('#skF_1', type, '#skF_1': $i).
% 8.25/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.25/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.25/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.25/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.25/3.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.25/3.01  
% 8.25/3.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.25/3.03  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 8.25/3.03  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.25/3.03  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 8.25/3.03  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 8.25/3.03  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.25/3.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.25/3.03  tff(c_12, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.25/3.03  tff(c_17, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 8.25/3.03  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.25/3.03  tff(c_85, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.25/3.03  tff(c_109, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_85])).
% 8.25/3.03  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.25/3.03  tff(c_127, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_109, c_10])).
% 8.25/3.03  tff(c_168, plain, (![A_25, B_26, C_27]: (k3_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k3_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.25/3.03  tff(c_199, plain, (![C_27]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_27))=k3_xboole_0('#skF_1', C_27))), inference(superposition, [status(thm), theory('equality')], [c_127, c_168])).
% 8.25/3.03  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.25/3.03  tff(c_107, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_85])).
% 8.25/3.03  tff(c_4015, plain, (![A_101, B_102, B_103]: (k3_xboole_0(A_101, k3_xboole_0(B_102, k2_xboole_0(k3_xboole_0(A_101, B_102), B_103)))=k3_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_10, c_168])).
% 8.25/3.03  tff(c_6568, plain, (![A_130, B_131]: (k3_xboole_0(A_130, k3_xboole_0(B_131, A_130))=k3_xboole_0(A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4015])).
% 8.25/3.03  tff(c_6735, plain, (![B_131]: (k3_xboole_0('#skF_1', k3_xboole_0(B_131, '#skF_2'))=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_131)))), inference(superposition, [status(thm), theory('equality')], [c_6568, c_199])).
% 8.25/3.03  tff(c_14523, plain, (![B_179]: (k3_xboole_0('#skF_1', k3_xboole_0(B_179, '#skF_2'))=k3_xboole_0('#skF_1', B_179))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_6735])).
% 8.25/3.03  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.25/3.03  tff(c_108, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_14, c_85])).
% 8.25/3.03  tff(c_1955, plain, (![A_70, B_71, C_72]: (k3_xboole_0(A_70, k3_xboole_0(k2_xboole_0(A_70, B_71), C_72))=k3_xboole_0(A_70, C_72))), inference(superposition, [status(thm), theory('equality')], [c_10, c_168])).
% 8.25/3.03  tff(c_2234, plain, (![C_74]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_74))=k3_xboole_0('#skF_3', C_74))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1955])).
% 8.25/3.03  tff(c_19, plain, (![B_14, A_15]: (k3_xboole_0(B_14, A_15)=k3_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.25/3.03  tff(c_34, plain, (![B_14, A_15]: (r1_tarski(k3_xboole_0(B_14, A_15), A_15))), inference(superposition, [status(thm), theory('equality')], [c_19, c_8])).
% 8.25/3.03  tff(c_181, plain, (![A_25, B_26, C_27]: (r1_tarski(k3_xboole_0(A_25, k3_xboole_0(B_26, C_27)), C_27))), inference(superposition, [status(thm), theory('equality')], [c_168, c_34])).
% 8.25/3.03  tff(c_2275, plain, (![A_25, C_74]: (r1_tarski(k3_xboole_0(A_25, k3_xboole_0('#skF_3', C_74)), k3_xboole_0('#skF_4', C_74)))), inference(superposition, [status(thm), theory('equality')], [c_2234, c_181])).
% 8.25/3.03  tff(c_14570, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14523, c_2275])).
% 8.25/3.03  tff(c_14783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_14570])).
% 8.25/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.03  
% 8.25/3.03  Inference rules
% 8.25/3.03  ----------------------
% 8.25/3.03  #Ref     : 0
% 8.25/3.03  #Sup     : 3575
% 8.25/3.03  #Fact    : 0
% 8.25/3.03  #Define  : 0
% 8.25/3.03  #Split   : 0
% 8.25/3.03  #Chain   : 0
% 8.25/3.03  #Close   : 0
% 8.25/3.03  
% 8.25/3.03  Ordering : KBO
% 8.25/3.03  
% 8.25/3.03  Simplification rules
% 8.25/3.03  ----------------------
% 8.25/3.03  #Subsume      : 86
% 8.25/3.03  #Demod        : 3978
% 8.25/3.03  #Tautology    : 2241
% 8.25/3.03  #SimpNegUnit  : 1
% 8.25/3.03  #BackRed      : 0
% 8.25/3.03  
% 8.25/3.03  #Partial instantiations: 0
% 8.25/3.03  #Strategies tried      : 1
% 8.25/3.03  
% 8.25/3.03  Timing (in seconds)
% 8.25/3.03  ----------------------
% 8.25/3.03  Preprocessing        : 0.25
% 8.25/3.03  Parsing              : 0.14
% 8.25/3.03  CNF conversion       : 0.02
% 8.25/3.03  Main loop            : 2.01
% 8.25/3.03  Inferencing          : 0.41
% 8.25/3.03  Reduction            : 1.20
% 8.25/3.03  Demodulation         : 1.07
% 8.25/3.03  BG Simplification    : 0.05
% 8.25/3.03  Subsumption          : 0.26
% 8.25/3.03  Abstraction          : 0.08
% 8.25/3.03  MUC search           : 0.00
% 8.25/3.03  Cooper               : 0.00
% 8.25/3.03  Total                : 2.30
% 8.25/3.03  Index Insertion      : 0.00
% 8.25/3.03  Index Deletion       : 0.00
% 8.25/3.03  Index Matching       : 0.00
% 8.25/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
