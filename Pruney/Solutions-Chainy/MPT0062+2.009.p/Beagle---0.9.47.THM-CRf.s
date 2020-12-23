%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:08 EST 2020

% Result     : Theorem 20.98s
% Output     : CNFRefutation 20.98s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_301,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_863,plain,(
    ! [A_73,C_74,B_75] : k2_xboole_0(k4_xboole_0(A_73,C_74),k4_xboole_0(B_75,C_74)) = k4_xboole_0(k2_xboole_0(A_73,B_75),C_74) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27434,plain,(
    ! [A_346,B_347,B_348] : k2_xboole_0(k4_xboole_0(A_346,B_347),k4_xboole_0(B_348,k3_xboole_0(A_346,B_347))) = k4_xboole_0(k2_xboole_0(A_346,B_348),k3_xboole_0(A_346,B_347)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_863])).

tff(c_27855,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_27434])).

tff(c_32,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27855,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.98/13.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.98/13.53  
% 20.98/13.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.98/13.53  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 20.98/13.53  
% 20.98/13.53  %Foreground sorts:
% 20.98/13.53  
% 20.98/13.53  
% 20.98/13.53  %Background operators:
% 20.98/13.53  
% 20.98/13.53  
% 20.98/13.53  %Foreground operators:
% 20.98/13.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.98/13.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.98/13.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.98/13.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.98/13.53  tff('#skF_2', type, '#skF_2': $i).
% 20.98/13.53  tff('#skF_1', type, '#skF_1': $i).
% 20.98/13.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.98/13.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.98/13.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.98/13.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.98/13.53  
% 20.98/13.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 20.98/13.54  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 20.98/13.54  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 20.98/13.54  tff(f_62, negated_conjecture, ~(![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 20.98/13.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.98/13.54  tff(c_279, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.98/13.54  tff(c_301, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 20.98/13.54  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.98/13.54  tff(c_863, plain, (![A_73, C_74, B_75]: (k2_xboole_0(k4_xboole_0(A_73, C_74), k4_xboole_0(B_75, C_74))=k4_xboole_0(k2_xboole_0(A_73, B_75), C_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.98/13.54  tff(c_27434, plain, (![A_346, B_347, B_348]: (k2_xboole_0(k4_xboole_0(A_346, B_347), k4_xboole_0(B_348, k3_xboole_0(A_346, B_347)))=k4_xboole_0(k2_xboole_0(A_346, B_348), k3_xboole_0(A_346, B_347)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_863])).
% 20.98/13.54  tff(c_27855, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_27434])).
% 20.98/13.54  tff(c_32, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.98/13.54  tff(c_81116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27855, c_32])).
% 20.98/13.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.98/13.54  
% 20.98/13.54  Inference rules
% 20.98/13.54  ----------------------
% 20.98/13.54  #Ref     : 4
% 20.98/13.54  #Sup     : 21508
% 20.98/13.54  #Fact    : 0
% 20.98/13.54  #Define  : 0
% 20.98/13.54  #Split   : 5
% 20.98/13.54  #Chain   : 0
% 20.98/13.54  #Close   : 0
% 20.98/13.54  
% 20.98/13.54  Ordering : KBO
% 20.98/13.54  
% 20.98/13.54  Simplification rules
% 20.98/13.54  ----------------------
% 20.98/13.54  #Subsume      : 4243
% 20.98/13.54  #Demod        : 18487
% 20.98/13.54  #Tautology    : 9649
% 20.98/13.54  #SimpNegUnit  : 0
% 20.98/13.54  #BackRed      : 4
% 20.98/13.54  
% 20.98/13.54  #Partial instantiations: 0
% 20.98/13.54  #Strategies tried      : 1
% 20.98/13.54  
% 20.98/13.54  Timing (in seconds)
% 20.98/13.54  ----------------------
% 20.98/13.54  Preprocessing        : 0.29
% 20.98/13.54  Parsing              : 0.16
% 20.98/13.54  CNF conversion       : 0.02
% 20.98/13.54  Main loop            : 12.44
% 20.98/13.54  Inferencing          : 1.44
% 20.98/13.54  Reduction            : 8.00
% 20.98/13.54  Demodulation         : 7.42
% 20.98/13.54  BG Simplification    : 0.21
% 20.98/13.54  Subsumption          : 2.27
% 20.98/13.54  Abstraction          : 0.39
% 20.98/13.54  MUC search           : 0.00
% 20.98/13.54  Cooper               : 0.00
% 20.98/13.54  Total                : 12.75
% 20.98/13.54  Index Insertion      : 0.00
% 20.98/13.54  Index Deletion       : 0.00
% 20.98/13.54  Index Matching       : 0.00
% 20.98/13.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
