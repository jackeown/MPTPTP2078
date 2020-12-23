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
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  60 expanded)
%              Number of equality atoms :   32 (  41 expanded)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_70,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_22])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_208,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,(
    ! [A_5,C_37] : k4_xboole_0(k3_xboole_0(A_5,k1_xboole_0),C_37) = k4_xboole_0(A_5,k2_xboole_0(A_5,C_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_208])).

tff(c_329,plain,(
    ! [A_38,C_39] : k4_xboole_0(k3_xboole_0(A_38,k1_xboole_0),C_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_262])).

tff(c_558,plain,(
    ! [A_43] : k3_xboole_0(A_43,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_329])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_563,plain,(
    ! [A_43] : k4_xboole_0(k2_xboole_0(A_43,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_6])).

tff(c_567,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_563])).

tff(c_24,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_53])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(k4_xboole_0(A_16,B_17),k4_xboole_0(B_17,A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),k4_xboole_0(B_17,A_16)) = k5_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_26,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_666,plain,(
    ! [A_47,C_48,B_49] : k2_xboole_0(k4_xboole_0(A_47,C_48),k4_xboole_0(B_49,C_48)) = k4_xboole_0(k2_xboole_0(A_47,B_49),C_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2465,plain,(
    ! [B_87] : k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_87),'#skF_3') = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_87,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_666])).

tff(c_2515,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3')) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_2465])).

tff(c_2522,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_61,c_2515])).

tff(c_2524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.61  
% 3.67/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.61  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.67/1.61  
% 3.67/1.61  %Foreground sorts:
% 3.67/1.61  
% 3.67/1.61  
% 3.67/1.61  %Background operators:
% 3.67/1.61  
% 3.67/1.61  
% 3.67/1.61  %Foreground operators:
% 3.67/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.67/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.61  
% 3.67/1.62  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.67/1.62  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 3.67/1.62  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.67/1.62  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.67/1.62  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.67/1.62  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.67/1.62  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.67/1.62  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 3.67/1.62  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 3.67/1.62  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.67/1.62  tff(c_70, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | k4_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.67/1.62  tff(c_22, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.67/1.62  tff(c_78, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_22])).
% 3.67/1.62  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.67/1.62  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.67/1.62  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.67/1.62  tff(c_79, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.67/1.62  tff(c_103, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_79])).
% 3.67/1.62  tff(c_208, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.67/1.62  tff(c_262, plain, (![A_5, C_37]: (k4_xboole_0(k3_xboole_0(A_5, k1_xboole_0), C_37)=k4_xboole_0(A_5, k2_xboole_0(A_5, C_37)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_208])).
% 3.67/1.62  tff(c_329, plain, (![A_38, C_39]: (k4_xboole_0(k3_xboole_0(A_38, k1_xboole_0), C_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_262])).
% 3.67/1.62  tff(c_558, plain, (![A_43]: (k3_xboole_0(A_43, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_329])).
% 3.67/1.62  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.67/1.62  tff(c_563, plain, (![A_43]: (k4_xboole_0(k2_xboole_0(A_43, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_558, c_6])).
% 3.67/1.62  tff(c_567, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_563])).
% 3.67/1.62  tff(c_24, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.67/1.62  tff(c_53, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.67/1.62  tff(c_61, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_53])).
% 3.67/1.62  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(k4_xboole_0(A_16, B_17), k4_xboole_0(B_17, A_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.67/1.62  tff(c_27, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), k4_xboole_0(B_17, A_16))=k5_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 3.67/1.62  tff(c_26, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.67/1.62  tff(c_60, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_53])).
% 3.67/1.62  tff(c_666, plain, (![A_47, C_48, B_49]: (k2_xboole_0(k4_xboole_0(A_47, C_48), k4_xboole_0(B_49, C_48))=k4_xboole_0(k2_xboole_0(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.67/1.62  tff(c_2465, plain, (![B_87]: (k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_87), '#skF_3')=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_87, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_666])).
% 3.67/1.62  tff(c_2515, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3'))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27, c_2465])).
% 3.67/1.62  tff(c_2522, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_567, c_61, c_2515])).
% 3.67/1.62  tff(c_2524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2522])).
% 3.67/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.62  
% 3.67/1.62  Inference rules
% 3.67/1.62  ----------------------
% 3.67/1.62  #Ref     : 0
% 3.67/1.62  #Sup     : 640
% 3.67/1.62  #Fact    : 0
% 3.67/1.62  #Define  : 0
% 3.67/1.62  #Split   : 0
% 3.67/1.62  #Chain   : 0
% 3.67/1.62  #Close   : 0
% 3.67/1.62  
% 3.67/1.62  Ordering : KBO
% 3.67/1.62  
% 3.67/1.62  Simplification rules
% 3.67/1.62  ----------------------
% 3.67/1.62  #Subsume      : 0
% 3.67/1.62  #Demod        : 422
% 3.67/1.62  #Tautology    : 358
% 3.67/1.62  #SimpNegUnit  : 1
% 3.67/1.62  #BackRed      : 3
% 3.67/1.62  
% 3.67/1.62  #Partial instantiations: 0
% 3.67/1.62  #Strategies tried      : 1
% 3.67/1.62  
% 3.67/1.62  Timing (in seconds)
% 3.67/1.62  ----------------------
% 3.67/1.63  Preprocessing        : 0.29
% 3.67/1.63  Parsing              : 0.17
% 3.67/1.63  CNF conversion       : 0.02
% 3.67/1.63  Main loop            : 0.54
% 3.67/1.63  Inferencing          : 0.18
% 3.67/1.63  Reduction            : 0.22
% 3.67/1.63  Demodulation         : 0.17
% 3.67/1.63  BG Simplification    : 0.03
% 3.67/1.63  Subsumption          : 0.08
% 3.67/1.63  Abstraction          : 0.03
% 3.67/1.63  MUC search           : 0.00
% 3.67/1.63  Cooper               : 0.00
% 3.67/1.63  Total                : 0.86
% 3.67/1.63  Index Insertion      : 0.00
% 3.67/1.63  Index Deletion       : 0.00
% 3.67/1.63  Index Matching       : 0.00
% 3.67/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
