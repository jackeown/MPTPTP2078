%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   33 (  54 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    5 (   3 average)
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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_74,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_73,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_96,plain,(
    ! [A_26,B_27,C_28] : k4_xboole_0(k4_xboole_0(A_26,B_27),C_28) = k4_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_4,C_28] : k4_xboole_0(A_4,k2_xboole_0(A_4,C_28)) = k4_xboole_0(k1_xboole_0,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_96])).

tff(c_161,plain,(
    ! [C_28] : k4_xboole_0(k1_xboole_0,C_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_258,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k4_xboole_0(A_32,B_33),k3_xboole_0(A_32,C_34)) = k4_xboole_0(A_32,k4_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_294,plain,(
    ! [A_4,C_34] : k4_xboole_0(A_4,k4_xboole_0(k1_xboole_0,C_34)) = k2_xboole_0(A_4,k3_xboole_0(A_4,C_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_258])).

tff(c_405,plain,(
    ! [A_39,C_40] : k2_xboole_0(A_39,k3_xboole_0(A_39,C_40)) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_161,c_294])).

tff(c_420,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_405])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3958,plain,(
    ! [A_117,B_118,C_119] : k4_xboole_0(k4_xboole_0(A_117,B_118),k4_xboole_0(A_117,k2_xboole_0(B_118,C_119))) = k3_xboole_0(k4_xboole_0(A_117,B_118),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_4127,plain,(
    ! [A_117,A_8] : k4_xboole_0(k4_xboole_0(A_117,A_8),k4_xboole_0(A_117,A_8)) = k3_xboole_0(k4_xboole_0(A_117,A_8),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_3958])).

tff(c_4215,plain,(
    ! [A_117,A_8] : k3_xboole_0(k4_xboole_0(A_117,A_8),A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4127])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_18])).

tff(c_4229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4215,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n005.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 15:31:17 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.61  
% 3.64/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.61  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.64/1.61  
% 3.64/1.61  %Foreground sorts:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Background operators:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Foreground operators:
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.61  
% 3.64/1.62  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.64/1.62  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.64/1.62  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.64/1.62  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.64/1.62  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.64/1.62  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.64/1.62  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.64/1.62  tff(f_44, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.64/1.62  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.62  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.62  tff(c_52, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.62  tff(c_70, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 3.64/1.62  tff(c_74, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_70])).
% 3.64/1.62  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.62  tff(c_67, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_52])).
% 3.64/1.62  tff(c_73, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 3.64/1.62  tff(c_96, plain, (![A_26, B_27, C_28]: (k4_xboole_0(k4_xboole_0(A_26, B_27), C_28)=k4_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.62  tff(c_130, plain, (![A_4, C_28]: (k4_xboole_0(A_4, k2_xboole_0(A_4, C_28))=k4_xboole_0(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_74, c_96])).
% 3.64/1.62  tff(c_161, plain, (![C_28]: (k4_xboole_0(k1_xboole_0, C_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_130])).
% 3.64/1.62  tff(c_258, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k3_xboole_0(A_32, C_34))=k4_xboole_0(A_32, k4_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.64/1.62  tff(c_294, plain, (![A_4, C_34]: (k4_xboole_0(A_4, k4_xboole_0(k1_xboole_0, C_34))=k2_xboole_0(A_4, k3_xboole_0(A_4, C_34)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_258])).
% 3.64/1.62  tff(c_405, plain, (![A_39, C_40]: (k2_xboole_0(A_39, k3_xboole_0(A_39, C_40))=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_161, c_294])).
% 3.64/1.62  tff(c_420, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_73, c_405])).
% 3.64/1.62  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.62  tff(c_3958, plain, (![A_117, B_118, C_119]: (k4_xboole_0(k4_xboole_0(A_117, B_118), k4_xboole_0(A_117, k2_xboole_0(B_118, C_119)))=k3_xboole_0(k4_xboole_0(A_117, B_118), C_119))), inference(superposition, [status(thm), theory('equality')], [c_96, c_14])).
% 3.64/1.62  tff(c_4127, plain, (![A_117, A_8]: (k4_xboole_0(k4_xboole_0(A_117, A_8), k4_xboole_0(A_117, A_8))=k3_xboole_0(k4_xboole_0(A_117, A_8), A_8))), inference(superposition, [status(thm), theory('equality')], [c_420, c_3958])).
% 3.64/1.62  tff(c_4215, plain, (![A_117, A_8]: (k3_xboole_0(k4_xboole_0(A_117, A_8), A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4127])).
% 3.64/1.62  tff(c_42, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.62  tff(c_18, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.62  tff(c_46, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_18])).
% 3.64/1.62  tff(c_4229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4215, c_46])).
% 3.64/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.62  
% 3.64/1.62  Inference rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Ref     : 0
% 3.64/1.62  #Sup     : 1019
% 3.64/1.62  #Fact    : 0
% 3.64/1.62  #Define  : 0
% 3.64/1.62  #Split   : 0
% 3.64/1.62  #Chain   : 0
% 3.64/1.62  #Close   : 0
% 3.64/1.62  
% 3.64/1.62  Ordering : KBO
% 3.64/1.62  
% 3.64/1.62  Simplification rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Subsume      : 0
% 3.64/1.62  #Demod        : 1047
% 3.64/1.62  #Tautology    : 714
% 3.64/1.62  #SimpNegUnit  : 0
% 3.64/1.62  #BackRed      : 4
% 3.64/1.62  
% 3.64/1.62  #Partial instantiations: 0
% 3.64/1.62  #Strategies tried      : 1
% 3.64/1.62  
% 3.64/1.62  Timing (in seconds)
% 3.64/1.62  ----------------------
% 3.64/1.62  Preprocessing        : 0.26
% 3.64/1.62  Parsing              : 0.15
% 3.64/1.62  CNF conversion       : 0.01
% 3.64/1.62  Main loop            : 0.67
% 3.64/1.62  Inferencing          : 0.24
% 3.64/1.62  Reduction            : 0.29
% 3.64/1.62  Demodulation         : 0.23
% 3.64/1.62  BG Simplification    : 0.03
% 3.64/1.62  Subsumption          : 0.08
% 3.64/1.62  Abstraction          : 0.04
% 3.64/1.62  MUC search           : 0.00
% 3.64/1.62  Cooper               : 0.00
% 3.64/1.62  Total                : 0.96
% 3.64/1.62  Index Insertion      : 0.00
% 3.64/1.62  Index Deletion       : 0.00
% 3.64/1.62  Index Matching       : 0.00
% 3.64/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
