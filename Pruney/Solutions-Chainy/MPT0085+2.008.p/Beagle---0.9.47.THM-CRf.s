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
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_210,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_228,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_210])).

tff(c_31,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_8])).

tff(c_243,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_47])).

tff(c_302,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k4_xboole_0(A_31,B_32),C_33) = k4_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_424,plain,(
    ! [C_35] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_35)) = k4_xboole_0('#skF_1',C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_302])).

tff(c_439,plain,(
    ! [C_35] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_35)) = k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_14])).

tff(c_911,plain,(
    ! [C_46] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_46)) = k3_xboole_0('#skF_1',C_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_439])).

tff(c_942,plain,(
    ! [B_2] : k3_xboole_0('#skF_1',k2_xboole_0(B_2,'#skF_2')) = k3_xboole_0('#skF_1',B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_911])).

tff(c_18,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.43  
% 3.07/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.43  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.07/1.43  
% 3.07/1.43  %Foreground sorts:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Background operators:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Foreground operators:
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.43  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.43  
% 3.07/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.07/1.44  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.07/1.44  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.07/1.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.07/1.44  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.07/1.44  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.07/1.44  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.07/1.44  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.44  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.44  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.44  tff(c_119, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.44  tff(c_127, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_119])).
% 3.07/1.44  tff(c_210, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.44  tff(c_228, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_127, c_210])).
% 3.07/1.44  tff(c_31, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.44  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.44  tff(c_47, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_31, c_8])).
% 3.07/1.44  tff(c_243, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_228, c_47])).
% 3.07/1.44  tff(c_302, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k4_xboole_0(A_31, B_32), C_33)=k4_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.44  tff(c_424, plain, (![C_35]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_35))=k4_xboole_0('#skF_1', C_35))), inference(superposition, [status(thm), theory('equality')], [c_243, c_302])).
% 3.07/1.44  tff(c_439, plain, (![C_35]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_35))=k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_35)))), inference(superposition, [status(thm), theory('equality')], [c_424, c_14])).
% 3.07/1.44  tff(c_911, plain, (![C_46]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_46))=k3_xboole_0('#skF_1', C_46))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_439])).
% 3.07/1.44  tff(c_942, plain, (![B_2]: (k3_xboole_0('#skF_1', k2_xboole_0(B_2, '#skF_2'))=k3_xboole_0('#skF_1', B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_911])).
% 3.07/1.44  tff(c_18, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.44  tff(c_21, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 3.07/1.44  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_21])).
% 3.07/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.44  
% 3.07/1.44  Inference rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Ref     : 0
% 3.07/1.44  #Sup     : 362
% 3.07/1.44  #Fact    : 0
% 3.07/1.44  #Define  : 0
% 3.07/1.44  #Split   : 0
% 3.07/1.44  #Chain   : 0
% 3.07/1.44  #Close   : 0
% 3.07/1.44  
% 3.07/1.44  Ordering : KBO
% 3.07/1.44  
% 3.07/1.44  Simplification rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Subsume      : 0
% 3.07/1.44  #Demod        : 345
% 3.07/1.44  #Tautology    : 232
% 3.07/1.44  #SimpNegUnit  : 0
% 3.07/1.44  #BackRed      : 2
% 3.07/1.44  
% 3.07/1.44  #Partial instantiations: 0
% 3.07/1.44  #Strategies tried      : 1
% 3.07/1.44  
% 3.07/1.44  Timing (in seconds)
% 3.07/1.44  ----------------------
% 3.07/1.45  Preprocessing        : 0.26
% 3.07/1.45  Parsing              : 0.14
% 3.07/1.45  CNF conversion       : 0.01
% 3.07/1.45  Main loop            : 0.44
% 3.07/1.45  Inferencing          : 0.15
% 3.07/1.45  Reduction            : 0.19
% 3.07/1.45  Demodulation         : 0.16
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.06
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.72
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
