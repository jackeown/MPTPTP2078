%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:46 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  64 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_18])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_104,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_89,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(k4_xboole_0(A_11,B_12),k4_xboole_0(B_12,A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [A_24,B_25] : k2_xboole_0(k4_xboole_0(A_24,B_25),k4_xboole_0(B_25,A_24)) = k5_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_174,plain,(
    ! [A_5] : k2_xboole_0(A_5,k4_xboole_0(k1_xboole_0,A_5)) = k5_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_135])).

tff(c_183,plain,(
    ! [A_26] : k2_xboole_0(A_26,k4_xboole_0(k1_xboole_0,A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_174])).

tff(c_197,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_183])).

tff(c_209,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_197])).

tff(c_22,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_23,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k4_xboole_0(B_12,A_11)) = k5_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_20,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_300,plain,(
    ! [A_30,C_31,B_32] : k2_xboole_0(k4_xboole_0(A_30,C_31),k4_xboole_0(B_32,C_31)) = k4_xboole_0(k2_xboole_0(A_30,B_32),C_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_670,plain,(
    ! [A_41] : k4_xboole_0(k2_xboole_0(A_41,k4_xboole_0('#skF_2','#skF_1')),'#skF_3') = k2_xboole_0(k4_xboole_0(A_41,'#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_300])).

tff(c_706,plain,(
    k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3'),k1_xboole_0) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_670])).

tff(c_710,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_59,c_706])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.35  
% 2.51/1.35  %Foreground sorts:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Background operators:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Foreground operators:
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.35  
% 2.51/1.36  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.51/1.36  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 2.51/1.36  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.51/1.36  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.51/1.36  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.51/1.36  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.51/1.36  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 2.51/1.36  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.51/1.36  tff(c_42, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.36  tff(c_18, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.36  tff(c_46, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_18])).
% 2.51/1.36  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.36  tff(c_68, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.36  tff(c_94, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.51/1.36  tff(c_104, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 2.51/1.36  tff(c_89, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.51/1.36  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.36  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(k4_xboole_0(A_11, B_12), k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.36  tff(c_135, plain, (![A_24, B_25]: (k2_xboole_0(k4_xboole_0(A_24, B_25), k4_xboole_0(B_25, A_24))=k5_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.51/1.36  tff(c_174, plain, (![A_5]: (k2_xboole_0(A_5, k4_xboole_0(k1_xboole_0, A_5))=k5_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_135])).
% 2.51/1.36  tff(c_183, plain, (![A_26]: (k2_xboole_0(A_26, k4_xboole_0(k1_xboole_0, A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_174])).
% 2.51/1.36  tff(c_197, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_183])).
% 2.51/1.36  tff(c_209, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_197])).
% 2.51/1.36  tff(c_22, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.36  tff(c_47, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.36  tff(c_59, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_47])).
% 2.51/1.36  tff(c_23, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k4_xboole_0(B_12, A_11))=k5_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.51/1.36  tff(c_20, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.36  tff(c_58, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_47])).
% 2.51/1.36  tff(c_300, plain, (![A_30, C_31, B_32]: (k2_xboole_0(k4_xboole_0(A_30, C_31), k4_xboole_0(B_32, C_31))=k4_xboole_0(k2_xboole_0(A_30, B_32), C_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.36  tff(c_670, plain, (![A_41]: (k4_xboole_0(k2_xboole_0(A_41, k4_xboole_0('#skF_2', '#skF_1')), '#skF_3')=k2_xboole_0(k4_xboole_0(A_41, '#skF_3'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_300])).
% 2.51/1.36  tff(c_706, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3'), k1_xboole_0)=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23, c_670])).
% 2.51/1.36  tff(c_710, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_59, c_706])).
% 2.51/1.36  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_710])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 183
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 0
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 0
% 2.51/1.36  #Demod        : 139
% 2.51/1.36  #Tautology    : 94
% 2.51/1.36  #SimpNegUnit  : 1
% 2.51/1.36  #BackRed      : 0
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.37  Preprocessing        : 0.29
% 2.51/1.37  Parsing              : 0.15
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.31
% 2.51/1.37  Inferencing          : 0.11
% 2.51/1.37  Reduction            : 0.12
% 2.51/1.37  Demodulation         : 0.09
% 2.51/1.37  BG Simplification    : 0.02
% 2.51/1.37  Subsumption          : 0.04
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.63
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
