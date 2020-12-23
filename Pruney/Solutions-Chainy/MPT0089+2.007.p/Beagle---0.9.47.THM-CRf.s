%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:24 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_102,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k4_xboole_0(A_23,B_24),C_25) = k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(B_24,k1_xboole_0)) = k4_xboole_0(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_6])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_xboole_0(A_2,k4_xboole_0(B_3,A_2)) = k2_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_73,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_112,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(B_24,k4_xboole_0(A_23,B_24))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_73])).

tff(c_159,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(B_24,A_23)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_4548,plain,(
    ! [C_106,A_107,B_108] : k2_xboole_0(C_106,k4_xboole_0(A_107,k2_xboole_0(B_108,C_106))) = k2_xboole_0(C_106,k4_xboole_0(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_4782,plain,(
    ! [A_109,B_110] : k2_xboole_0(A_109,k4_xboole_0(A_109,B_110)) = k2_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_4548])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_23,B_24,C_25] : r1_xboole_0(k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_4856,plain,(
    ! [A_23,A_109,B_110] : r1_xboole_0(k4_xboole_0(A_23,k2_xboole_0(A_109,k1_xboole_0)),k4_xboole_0(A_109,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4782,c_125])).

tff(c_4979,plain,(
    ! [A_23,A_109,B_110] : r1_xboole_0(k4_xboole_0(A_23,A_109),k4_xboole_0(A_109,B_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_4856])).

tff(c_14,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.75  
% 4.09/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.75  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.37/1.75  
% 4.37/1.75  %Foreground sorts:
% 4.37/1.75  
% 4.37/1.75  
% 4.37/1.75  %Background operators:
% 4.37/1.75  
% 4.37/1.75  
% 4.37/1.75  %Foreground operators:
% 4.37/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.37/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.75  
% 4.37/1.76  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.37/1.76  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.37/1.76  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.37/1.76  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.37/1.76  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.37/1.76  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.37/1.76  tff(f_40, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 4.37/1.76  tff(c_102, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k4_xboole_0(A_23, B_24), C_25)=k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.76  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.76  tff(c_129, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(B_24, k1_xboole_0))=k4_xboole_0(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_102, c_6])).
% 4.37/1.76  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, k4_xboole_0(B_3, A_2))=k2_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.37/1.76  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.76  tff(c_49, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.76  tff(c_70, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 4.37/1.76  tff(c_73, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_70])).
% 4.37/1.76  tff(c_112, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(B_24, k4_xboole_0(A_23, B_24)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_73])).
% 4.37/1.76  tff(c_159, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(B_24, A_23))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_112])).
% 4.37/1.76  tff(c_4548, plain, (![C_106, A_107, B_108]: (k2_xboole_0(C_106, k4_xboole_0(A_107, k2_xboole_0(B_108, C_106)))=k2_xboole_0(C_106, k4_xboole_0(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 4.37/1.76  tff(c_4782, plain, (![A_109, B_110]: (k2_xboole_0(A_109, k4_xboole_0(A_109, B_110))=k2_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_4548])).
% 4.37/1.76  tff(c_12, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.76  tff(c_125, plain, (![A_23, B_24, C_25]: (r1_xboole_0(k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)), C_25))), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 4.37/1.76  tff(c_4856, plain, (![A_23, A_109, B_110]: (r1_xboole_0(k4_xboole_0(A_23, k2_xboole_0(A_109, k1_xboole_0)), k4_xboole_0(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_4782, c_125])).
% 4.37/1.76  tff(c_4979, plain, (![A_23, A_109, B_110]: (r1_xboole_0(k4_xboole_0(A_23, A_109), k4_xboole_0(A_109, B_110)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_4856])).
% 4.37/1.76  tff(c_14, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.76  tff(c_5008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4979, c_14])).
% 4.37/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  
% 4.37/1.76  Inference rules
% 4.37/1.76  ----------------------
% 4.37/1.76  #Ref     : 0
% 4.37/1.76  #Sup     : 1202
% 4.37/1.76  #Fact    : 0
% 4.37/1.76  #Define  : 0
% 4.37/1.76  #Split   : 0
% 4.37/1.76  #Chain   : 0
% 4.37/1.76  #Close   : 0
% 4.37/1.76  
% 4.37/1.76  Ordering : KBO
% 4.37/1.76  
% 4.37/1.76  Simplification rules
% 4.37/1.76  ----------------------
% 4.37/1.76  #Subsume      : 8
% 4.37/1.76  #Demod        : 1081
% 4.37/1.76  #Tautology    : 853
% 4.37/1.76  #SimpNegUnit  : 0
% 4.37/1.76  #BackRed      : 2
% 4.37/1.76  
% 4.37/1.76  #Partial instantiations: 0
% 4.37/1.76  #Strategies tried      : 1
% 4.37/1.76  
% 4.37/1.76  Timing (in seconds)
% 4.37/1.76  ----------------------
% 4.37/1.76  Preprocessing        : 0.25
% 4.37/1.76  Parsing              : 0.14
% 4.37/1.76  CNF conversion       : 0.01
% 4.37/1.76  Main loop            : 0.74
% 4.37/1.76  Inferencing          : 0.25
% 4.37/1.76  Reduction            : 0.31
% 4.37/1.76  Demodulation         : 0.26
% 4.37/1.76  BG Simplification    : 0.03
% 4.37/1.76  Subsumption          : 0.10
% 4.37/1.76  Abstraction          : 0.04
% 4.37/1.76  MUC search           : 0.00
% 4.37/1.76  Cooper               : 0.00
% 4.37/1.76  Total                : 1.02
% 4.37/1.76  Index Insertion      : 0.00
% 4.37/1.76  Index Deletion       : 0.00
% 4.37/1.76  Index Matching       : 0.00
% 4.37/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
