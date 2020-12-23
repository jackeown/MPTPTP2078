%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  86 expanded)
%              Number of equality atoms :   38 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_138,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_28])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_334,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,B_39),k4_xboole_0(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_379,plain,(
    ! [A_8] : k2_xboole_0(k3_xboole_0(A_8,k1_xboole_0),A_8) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_334])).

tff(c_393,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_379])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_395,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k4_xboole_0(A_40,B_41),k3_xboole_0(A_40,C_42)) = k4_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_425,plain,(
    ! [C_42] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_42)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_395])).

tff(c_466,plain,(
    ! [C_42] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_42)) = k3_xboole_0('#skF_1',C_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_425])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_184,plain,(
    ! [A_33] : k4_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_33] : k4_xboole_0(A_33,k1_xboole_0) = k3_xboole_0(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_18])).

tff(c_201,plain,(
    ! [A_33] : k3_xboole_0(A_33,A_33) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_183,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_358,plain,(
    ! [A_8] : k2_xboole_0(k3_xboole_0(A_8,A_8),k1_xboole_0) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_334])).

tff(c_389,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_358])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_128,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_128])).

tff(c_428,plain,(
    ! [B_41] : k4_xboole_0('#skF_1',k4_xboole_0(B_41,k3_xboole_0('#skF_3','#skF_2'))) = k2_xboole_0(k4_xboole_0('#skF_1',B_41),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_395])).

tff(c_606,plain,(
    ! [B_48] : k4_xboole_0('#skF_1',k4_xboole_0(B_48,k3_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1',B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_428])).

tff(c_648,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_606])).

tff(c_666,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_151,c_648])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.35  
% 2.45/1.37  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.45/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.45/1.37  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.37  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.37  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.45/1.37  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.45/1.37  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.45/1.37  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.45/1.37  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.45/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.45/1.37  tff(c_138, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.37  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.37  tff(c_146, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_28])).
% 2.45/1.37  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.37  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.37  tff(c_334, plain, (![A_38, B_39]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k4_xboole_0(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.37  tff(c_379, plain, (![A_8]: (k2_xboole_0(k3_xboole_0(A_8, k1_xboole_0), A_8)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_14, c_334])).
% 2.45/1.37  tff(c_393, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_379])).
% 2.45/1.37  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.37  tff(c_147, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.37  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_147])).
% 2.45/1.37  tff(c_395, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k4_xboole_0(A_40, B_41), k3_xboole_0(A_40, C_42))=k4_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.45/1.37  tff(c_425, plain, (![C_42]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_42))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_42)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_395])).
% 2.45/1.37  tff(c_466, plain, (![C_42]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_42))=k3_xboole_0('#skF_1', C_42))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_425])).
% 2.45/1.37  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.37  tff(c_161, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.37  tff(c_179, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_161])).
% 2.45/1.37  tff(c_184, plain, (![A_33]: (k4_xboole_0(A_33, A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.45/1.37  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.37  tff(c_189, plain, (![A_33]: (k4_xboole_0(A_33, k1_xboole_0)=k3_xboole_0(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_184, c_18])).
% 2.45/1.37  tff(c_201, plain, (![A_33]: (k3_xboole_0(A_33, A_33)=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_189])).
% 2.45/1.37  tff(c_183, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.45/1.37  tff(c_358, plain, (![A_8]: (k2_xboole_0(k3_xboole_0(A_8, A_8), k1_xboole_0)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_183, c_334])).
% 2.45/1.37  tff(c_389, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_358])).
% 2.45/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.37  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.37  tff(c_29, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 2.45/1.37  tff(c_128, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.37  tff(c_132, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_128])).
% 2.45/1.37  tff(c_428, plain, (![B_41]: (k4_xboole_0('#skF_1', k4_xboole_0(B_41, k3_xboole_0('#skF_3', '#skF_2')))=k2_xboole_0(k4_xboole_0('#skF_1', B_41), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_395])).
% 2.45/1.37  tff(c_606, plain, (![B_48]: (k4_xboole_0('#skF_1', k4_xboole_0(B_48, k3_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', B_48))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_428])).
% 2.45/1.37  tff(c_648, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_606])).
% 2.45/1.37  tff(c_666, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_466, c_151, c_648])).
% 2.45/1.37  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_666])).
% 2.45/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  Inference rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Ref     : 0
% 2.45/1.37  #Sup     : 156
% 2.45/1.37  #Fact    : 0
% 2.45/1.37  #Define  : 0
% 2.45/1.37  #Split   : 0
% 2.45/1.37  #Chain   : 0
% 2.45/1.37  #Close   : 0
% 2.45/1.37  
% 2.45/1.37  Ordering : KBO
% 2.45/1.37  
% 2.45/1.37  Simplification rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Subsume      : 0
% 2.45/1.37  #Demod        : 96
% 2.45/1.37  #Tautology    : 106
% 2.45/1.37  #SimpNegUnit  : 1
% 2.45/1.37  #BackRed      : 0
% 2.45/1.37  
% 2.45/1.37  #Partial instantiations: 0
% 2.45/1.37  #Strategies tried      : 1
% 2.45/1.37  
% 2.45/1.37  Timing (in seconds)
% 2.45/1.37  ----------------------
% 2.45/1.37  Preprocessing        : 0.27
% 2.45/1.37  Parsing              : 0.15
% 2.45/1.37  CNF conversion       : 0.02
% 2.45/1.37  Main loop            : 0.29
% 2.45/1.37  Inferencing          : 0.10
% 2.45/1.37  Reduction            : 0.12
% 2.45/1.37  Demodulation         : 0.10
% 2.45/1.37  BG Simplification    : 0.01
% 2.45/1.37  Subsumption          : 0.04
% 2.45/1.37  Abstraction          : 0.02
% 2.45/1.37  MUC search           : 0.00
% 2.45/1.37  Cooper               : 0.00
% 2.45/1.37  Total                : 0.59
% 2.45/1.37  Index Insertion      : 0.00
% 2.45/1.37  Index Deletion       : 0.00
% 2.45/1.37  Index Matching       : 0.00
% 2.45/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
