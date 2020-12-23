%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  39 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k4_xboole_0(A_25,B_26),C_27) = k4_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_61,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_151,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(B_26,k4_xboole_0(A_25,B_26))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_61])).

tff(c_192,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(B_26,A_25)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_147,plain,(
    ! [C_27,A_25,B_26] : k2_xboole_0(C_27,k4_xboole_0(A_25,k2_xboole_0(B_26,C_27))) = k2_xboole_0(C_27,k4_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_25,B_26,B_11] : k4_xboole_0(A_25,k2_xboole_0(B_26,k4_xboole_0(k4_xboole_0(A_25,B_26),B_11))) = k3_xboole_0(k4_xboole_0(A_25,B_26),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_14])).

tff(c_6157,plain,(
    ! [A_123,B_124,B_125] : k4_xboole_0(A_123,k2_xboole_0(B_124,k4_xboole_0(A_123,k2_xboole_0(B_124,B_125)))) = k3_xboole_0(k4_xboole_0(A_123,B_124),B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_158])).

tff(c_6311,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(B_26,k4_xboole_0(A_25,B_26))) = k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_6157])).

tff(c_6464,plain,(
    ! [A_25,B_26] : k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_8,c_6311])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_16])).

tff(c_6501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6464,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.89  
% 4.54/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.89  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.54/1.89  
% 4.54/1.89  %Foreground sorts:
% 4.54/1.89  
% 4.54/1.89  
% 4.54/1.89  %Background operators:
% 4.54/1.89  
% 4.54/1.89  
% 4.54/1.89  %Foreground operators:
% 4.54/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.89  
% 4.54/1.90  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.54/1.90  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.54/1.90  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.54/1.90  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.54/1.90  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.54/1.90  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.54/1.90  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.54/1.90  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.54/1.90  tff(c_138, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k4_xboole_0(A_25, B_26), C_27)=k4_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.54/1.90  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.90  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.54/1.90  tff(c_43, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.90  tff(c_58, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_43])).
% 4.54/1.90  tff(c_61, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 4.54/1.90  tff(c_151, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(B_26, k4_xboole_0(A_25, B_26)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_61])).
% 4.54/1.90  tff(c_192, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(B_26, A_25))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 4.54/1.90  tff(c_147, plain, (![C_27, A_25, B_26]: (k2_xboole_0(C_27, k4_xboole_0(A_25, k2_xboole_0(B_26, C_27)))=k2_xboole_0(C_27, k4_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_8])).
% 4.54/1.90  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.54/1.90  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.90  tff(c_158, plain, (![A_25, B_26, B_11]: (k4_xboole_0(A_25, k2_xboole_0(B_26, k4_xboole_0(k4_xboole_0(A_25, B_26), B_11)))=k3_xboole_0(k4_xboole_0(A_25, B_26), B_11))), inference(superposition, [status(thm), theory('equality')], [c_138, c_14])).
% 4.54/1.90  tff(c_6157, plain, (![A_123, B_124, B_125]: (k4_xboole_0(A_123, k2_xboole_0(B_124, k4_xboole_0(A_123, k2_xboole_0(B_124, B_125))))=k3_xboole_0(k4_xboole_0(A_123, B_124), B_125))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_158])).
% 4.54/1.90  tff(c_6311, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(B_26, k4_xboole_0(A_25, B_26)))=k3_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(superposition, [status(thm), theory('equality')], [c_147, c_6157])).
% 4.54/1.90  tff(c_6464, plain, (![A_25, B_26]: (k3_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_8, c_6311])).
% 4.54/1.90  tff(c_34, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.54/1.90  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.54/1.90  tff(c_42, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_16])).
% 4.54/1.90  tff(c_6501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6464, c_42])).
% 4.54/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.90  
% 4.54/1.90  Inference rules
% 4.54/1.90  ----------------------
% 4.54/1.90  #Ref     : 0
% 4.54/1.90  #Sup     : 1549
% 4.54/1.90  #Fact    : 0
% 4.54/1.90  #Define  : 0
% 4.54/1.90  #Split   : 0
% 4.54/1.90  #Chain   : 0
% 4.54/1.90  #Close   : 0
% 4.54/1.90  
% 4.54/1.90  Ordering : KBO
% 4.54/1.90  
% 4.54/1.90  Simplification rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Subsume      : 9
% 4.67/1.90  #Demod        : 1368
% 4.67/1.90  #Tautology    : 992
% 4.67/1.90  #SimpNegUnit  : 0
% 4.67/1.90  #BackRed      : 1
% 4.67/1.90  
% 4.67/1.90  #Partial instantiations: 0
% 4.67/1.90  #Strategies tried      : 1
% 4.67/1.90  
% 4.67/1.90  Timing (in seconds)
% 4.67/1.90  ----------------------
% 4.67/1.91  Preprocessing        : 0.25
% 4.67/1.91  Parsing              : 0.14
% 4.67/1.91  CNF conversion       : 0.01
% 4.67/1.91  Main loop            : 0.91
% 4.67/1.91  Inferencing          : 0.29
% 4.67/1.91  Reduction            : 0.40
% 4.67/1.91  Demodulation         : 0.33
% 4.67/1.91  BG Simplification    : 0.03
% 4.67/1.91  Subsumption          : 0.12
% 4.67/1.91  Abstraction          : 0.05
% 4.67/1.91  MUC search           : 0.00
% 4.67/1.91  Cooper               : 0.00
% 4.67/1.91  Total                : 1.19
% 4.67/1.91  Index Insertion      : 0.00
% 4.67/1.91  Index Deletion       : 0.00
% 4.67/1.91  Index Matching       : 0.00
% 4.67/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
