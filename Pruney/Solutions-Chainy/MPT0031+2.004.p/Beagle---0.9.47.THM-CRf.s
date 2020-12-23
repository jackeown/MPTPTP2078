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
% DateTime   : Thu Dec  3 09:42:36 EST 2020

% Result     : Theorem 13.03s
% Output     : CNFRefutation 13.03s
% Verified   : 
% Statistics : Number of formulae       :   32 (  48 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  40 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_501,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k3_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1641,plain,(
    ! [B_62,A_63,C_64] : k2_xboole_0(k3_xboole_0(B_62,A_63),k3_xboole_0(A_63,C_64)) = k3_xboole_0(A_63,k2_xboole_0(B_62,C_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_501])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_xboole_0(A_21,B_22),C_23) = k2_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_5,B_6,C_23] : k2_xboole_0(A_5,k2_xboole_0(k3_xboole_0(A_5,B_6),C_23)) = k2_xboole_0(A_5,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_1681,plain,(
    ! [B_62,A_63,C_64] : k2_xboole_0(B_62,k3_xboole_0(A_63,k2_xboole_0(B_62,C_64))) = k2_xboole_0(B_62,k3_xboole_0(A_63,C_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_155])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_555,plain,(
    ! [A_3,C_40] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_40)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_501])).

tff(c_569,plain,(
    ! [A_3,C_40] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_40)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_555])).

tff(c_2366,plain,(
    ! [A_75,B_76,B_77] : k2_xboole_0(k3_xboole_0(A_75,B_76),k3_xboole_0(B_77,A_75)) = k3_xboole_0(A_75,k2_xboole_0(B_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_501])).

tff(c_8942,plain,(
    ! [B_158,A_159,B_160] : k2_xboole_0(k3_xboole_0(B_158,A_159),k3_xboole_0(B_160,A_159)) = k3_xboole_0(A_159,k2_xboole_0(B_158,B_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2366])).

tff(c_9145,plain,(
    ! [A_3,C_40,B_160] : k3_xboole_0(k2_xboole_0(A_3,C_40),k2_xboole_0(A_3,B_160)) = k2_xboole_0(A_3,k3_xboole_0(B_160,k2_xboole_0(A_3,C_40))) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_8942])).

tff(c_9224,plain,(
    ! [A_3,C_40,B_160] : k3_xboole_0(k2_xboole_0(A_3,C_40),k2_xboole_0(A_3,B_160)) = k2_xboole_0(A_3,k3_xboole_0(B_160,C_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_9145])).

tff(c_12,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_12])).

tff(c_30493,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9224,c_13])).

tff(c_30497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:56:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.03/5.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.03/5.80  
% 13.03/5.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.03/5.80  %$ k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 13.03/5.80  
% 13.03/5.80  %Foreground sorts:
% 13.03/5.80  
% 13.03/5.80  
% 13.03/5.80  %Background operators:
% 13.03/5.80  
% 13.03/5.80  
% 13.03/5.80  %Foreground operators:
% 13.03/5.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.03/5.80  tff('#skF_2', type, '#skF_2': $i).
% 13.03/5.80  tff('#skF_3', type, '#skF_3': $i).
% 13.03/5.80  tff('#skF_1', type, '#skF_1': $i).
% 13.03/5.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.03/5.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.03/5.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.03/5.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.03/5.80  
% 13.03/5.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.03/5.81  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 13.03/5.81  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 13.03/5.81  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 13.03/5.81  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.03/5.81  tff(f_38, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 13.03/5.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.03/5.81  tff(c_501, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40))=k3_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.03/5.81  tff(c_1641, plain, (![B_62, A_63, C_64]: (k2_xboole_0(k3_xboole_0(B_62, A_63), k3_xboole_0(A_63, C_64))=k3_xboole_0(A_63, k2_xboole_0(B_62, C_64)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_501])).
% 13.03/5.81  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.03/5.81  tff(c_114, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_xboole_0(A_21, B_22), C_23)=k2_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.03/5.81  tff(c_155, plain, (![A_5, B_6, C_23]: (k2_xboole_0(A_5, k2_xboole_0(k3_xboole_0(A_5, B_6), C_23))=k2_xboole_0(A_5, C_23))), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 13.03/5.81  tff(c_1681, plain, (![B_62, A_63, C_64]: (k2_xboole_0(B_62, k3_xboole_0(A_63, k2_xboole_0(B_62, C_64)))=k2_xboole_0(B_62, k3_xboole_0(A_63, C_64)))), inference(superposition, [status(thm), theory('equality')], [c_1641, c_155])).
% 13.03/5.81  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.03/5.81  tff(c_555, plain, (![A_3, C_40]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_40))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_501])).
% 13.03/5.81  tff(c_569, plain, (![A_3, C_40]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_40))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_555])).
% 13.03/5.81  tff(c_2366, plain, (![A_75, B_76, B_77]: (k2_xboole_0(k3_xboole_0(A_75, B_76), k3_xboole_0(B_77, A_75))=k3_xboole_0(A_75, k2_xboole_0(B_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_501])).
% 13.03/5.81  tff(c_8942, plain, (![B_158, A_159, B_160]: (k2_xboole_0(k3_xboole_0(B_158, A_159), k3_xboole_0(B_160, A_159))=k3_xboole_0(A_159, k2_xboole_0(B_158, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2366])).
% 13.03/5.81  tff(c_9145, plain, (![A_3, C_40, B_160]: (k3_xboole_0(k2_xboole_0(A_3, C_40), k2_xboole_0(A_3, B_160))=k2_xboole_0(A_3, k3_xboole_0(B_160, k2_xboole_0(A_3, C_40))))), inference(superposition, [status(thm), theory('equality')], [c_569, c_8942])).
% 13.03/5.81  tff(c_9224, plain, (![A_3, C_40, B_160]: (k3_xboole_0(k2_xboole_0(A_3, C_40), k2_xboole_0(A_3, B_160))=k2_xboole_0(A_3, k3_xboole_0(B_160, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_9145])).
% 13.03/5.81  tff(c_12, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.03/5.81  tff(c_13, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_12])).
% 13.03/5.81  tff(c_30493, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9224, c_13])).
% 13.03/5.81  tff(c_30497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_30493])).
% 13.03/5.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.03/5.81  
% 13.03/5.81  Inference rules
% 13.03/5.81  ----------------------
% 13.03/5.81  #Ref     : 0
% 13.03/5.81  #Sup     : 7414
% 13.03/5.81  #Fact    : 0
% 13.03/5.81  #Define  : 0
% 13.03/5.81  #Split   : 0
% 13.03/5.81  #Chain   : 0
% 13.03/5.81  #Close   : 0
% 13.03/5.81  
% 13.03/5.81  Ordering : KBO
% 13.03/5.81  
% 13.03/5.81  Simplification rules
% 13.03/5.81  ----------------------
% 13.03/5.81  #Subsume      : 146
% 13.03/5.81  #Demod        : 10238
% 13.03/5.81  #Tautology    : 4504
% 13.03/5.81  #SimpNegUnit  : 0
% 13.03/5.81  #BackRed      : 3
% 13.03/5.81  
% 13.03/5.81  #Partial instantiations: 0
% 13.03/5.81  #Strategies tried      : 1
% 13.03/5.81  
% 13.03/5.81  Timing (in seconds)
% 13.03/5.81  ----------------------
% 13.03/5.81  Preprocessing        : 0.27
% 13.03/5.81  Parsing              : 0.15
% 13.03/5.81  CNF conversion       : 0.02
% 13.03/5.81  Main loop            : 4.74
% 13.03/5.81  Inferencing          : 0.96
% 13.03/5.81  Reduction            : 3.02
% 13.03/5.81  Demodulation         : 2.82
% 13.03/5.81  BG Simplification    : 0.13
% 13.03/5.81  Subsumption          : 0.50
% 13.03/5.81  Abstraction          : 0.27
% 13.03/5.81  MUC search           : 0.00
% 13.03/5.81  Cooper               : 0.00
% 13.03/5.82  Total                : 5.03
% 13.03/5.82  Index Insertion      : 0.00
% 13.03/5.82  Index Deletion       : 0.00
% 13.03/5.82  Index Matching       : 0.00
% 13.03/5.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
