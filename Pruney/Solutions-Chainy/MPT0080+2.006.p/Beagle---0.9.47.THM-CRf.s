%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 139 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 151 expanded)
%              Number of equality atoms :   47 (  95 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_161,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [A_43] : k3_xboole_0(A_43,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_161])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [A_43] : r1_tarski(k1_xboole_0,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_14])).

tff(c_211,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_285,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(resolution,[status(thm)],[c_184,c_211])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_294,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_2])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_240,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_211])).

tff(c_168,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_161])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_577,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_592,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_577])).

tff(c_595,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_592])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_836,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k4_xboole_0(A_67,B_68),C_69) = k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4133,plain,(
    ! [A_130,C_131] : k4_xboole_0(A_130,k2_xboole_0(A_130,C_131)) = k4_xboole_0(k1_xboole_0,C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_836])).

tff(c_4224,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4133])).

tff(c_4237,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_4224])).

tff(c_866,plain,(
    ! [A_13,C_69] : k4_xboole_0(A_13,k2_xboole_0(A_13,C_69)) = k4_xboole_0(k1_xboole_0,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_836])).

tff(c_4295,plain,(
    ! [A_133,C_134] : k4_xboole_0(A_133,k2_xboole_0(A_133,C_134)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4237,c_866])).

tff(c_4373,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_4295])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_877,plain,(
    ! [A_67,B_68,B_18] : k4_xboole_0(A_67,k2_xboole_0(B_68,k4_xboole_0(k4_xboole_0(A_67,B_68),B_18))) = k3_xboole_0(k4_xboole_0(A_67,B_68),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_836])).

tff(c_9007,plain,(
    ! [A_184,B_185,B_186] : k4_xboole_0(A_184,k2_xboole_0(B_185,k4_xboole_0(A_184,k2_xboole_0(B_185,B_186)))) = k3_xboole_0(k4_xboole_0(A_184,B_185),B_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_877])).

tff(c_9124,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4373,c_9007])).

tff(c_9257,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_4,c_9124])).

tff(c_239,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_14,c_211])).

tff(c_13618,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9257,c_239])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_169,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_4405,plain,(
    ! [A_135,B_136] : k4_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = k3_xboole_0(A_135,k4_xboole_0(A_135,B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_20])).

tff(c_4445,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_4405])).

tff(c_4463,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4445])).

tff(c_59,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_14])).

tff(c_460,plain,(
    ! [B_54,A_55] : k2_xboole_0(k3_xboole_0(B_54,A_55),A_55) = A_55 ),
    inference(resolution,[status(thm)],[c_74,c_211])).

tff(c_507,plain,(
    ! [B_2,B_54] : k2_xboole_0(B_2,k3_xboole_0(B_54,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_460])).

tff(c_667,plain,(
    ! [A_62,B_63,C_64] : k2_xboole_0(k2_xboole_0(A_62,B_63),C_64) = k2_xboole_0(A_62,k2_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [A_38,B_37] : r1_tarski(A_38,k2_xboole_0(B_37,A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_26])).

tff(c_946,plain,(
    ! [C_71,A_72,B_73] : r1_tarski(C_71,k2_xboole_0(A_72,k2_xboole_0(B_73,C_71))) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_123])).

tff(c_1494,plain,(
    ! [B_88,B_89,A_90] : r1_tarski(k3_xboole_0(B_88,B_89),k2_xboole_0(A_90,B_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_946])).

tff(c_1545,plain,(
    ! [B_88,A_1,B_2] : r1_tarski(k3_xboole_0(B_88,A_1),k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1494])).

tff(c_4477,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4463,c_1545])).

tff(c_14063,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13618,c_4477])).

tff(c_14167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_14063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.40/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.85  
% 7.40/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.86  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.40/2.86  
% 7.40/2.86  %Foreground sorts:
% 7.40/2.86  
% 7.40/2.86  
% 7.40/2.86  %Background operators:
% 7.40/2.86  
% 7.40/2.86  
% 7.40/2.86  %Foreground operators:
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.40/2.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.40/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.40/2.86  tff('#skF_2', type, '#skF_2': $i).
% 7.40/2.86  tff('#skF_3', type, '#skF_3': $i).
% 7.40/2.86  tff('#skF_1', type, '#skF_1': $i).
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.40/2.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.40/2.86  
% 7.40/2.87  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.40/2.87  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.40/2.87  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.40/2.87  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.40/2.87  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.40/2.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.40/2.87  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.40/2.87  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.40/2.87  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.40/2.87  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.40/2.87  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.40/2.87  tff(f_49, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.40/2.87  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.40/2.87  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.40/2.87  tff(c_24, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.40/2.87  tff(c_161, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.40/2.87  tff(c_170, plain, (![A_43]: (k3_xboole_0(A_43, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_161])).
% 7.40/2.87  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.40/2.87  tff(c_184, plain, (![A_43]: (r1_tarski(k1_xboole_0, A_43))), inference(superposition, [status(thm), theory('equality')], [c_170, c_14])).
% 7.40/2.87  tff(c_211, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.40/2.87  tff(c_285, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, A_48)=A_48)), inference(resolution, [status(thm)], [c_184, c_211])).
% 7.40/2.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.40/2.87  tff(c_294, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_285, c_2])).
% 7.40/2.87  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.40/2.87  tff(c_32, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.40/2.87  tff(c_33, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 7.40/2.87  tff(c_240, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_33, c_211])).
% 7.40/2.87  tff(c_168, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_161])).
% 7.40/2.87  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.40/2.87  tff(c_577, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.40/2.87  tff(c_592, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_577])).
% 7.40/2.87  tff(c_595, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_592])).
% 7.40/2.87  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.40/2.87  tff(c_836, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k4_xboole_0(A_67, B_68), C_69)=k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.40/2.87  tff(c_4133, plain, (![A_130, C_131]: (k4_xboole_0(A_130, k2_xboole_0(A_130, C_131))=k4_xboole_0(k1_xboole_0, C_131))), inference(superposition, [status(thm), theory('equality')], [c_595, c_836])).
% 7.40/2.87  tff(c_4224, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4133])).
% 7.40/2.87  tff(c_4237, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_595, c_4224])).
% 7.40/2.87  tff(c_866, plain, (![A_13, C_69]: (k4_xboole_0(A_13, k2_xboole_0(A_13, C_69))=k4_xboole_0(k1_xboole_0, C_69))), inference(superposition, [status(thm), theory('equality')], [c_595, c_836])).
% 7.40/2.87  tff(c_4295, plain, (![A_133, C_134]: (k4_xboole_0(A_133, k2_xboole_0(A_133, C_134))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4237, c_866])).
% 7.40/2.87  tff(c_4373, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_240, c_4295])).
% 7.40/2.87  tff(c_18, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.40/2.87  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.40/2.87  tff(c_877, plain, (![A_67, B_68, B_18]: (k4_xboole_0(A_67, k2_xboole_0(B_68, k4_xboole_0(k4_xboole_0(A_67, B_68), B_18)))=k3_xboole_0(k4_xboole_0(A_67, B_68), B_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_836])).
% 7.40/2.87  tff(c_9007, plain, (![A_184, B_185, B_186]: (k4_xboole_0(A_184, k2_xboole_0(B_185, k4_xboole_0(A_184, k2_xboole_0(B_185, B_186))))=k3_xboole_0(k4_xboole_0(A_184, B_185), B_186))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_877])).
% 7.40/2.87  tff(c_9124, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4373, c_9007])).
% 7.40/2.87  tff(c_9257, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_4, c_9124])).
% 7.40/2.87  tff(c_239, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_14, c_211])).
% 7.40/2.87  tff(c_13618, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_9257, c_239])).
% 7.40/2.87  tff(c_30, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.40/2.87  tff(c_169, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_161])).
% 7.40/2.87  tff(c_4405, plain, (![A_135, B_136]: (k4_xboole_0(A_135, k3_xboole_0(A_135, B_136))=k3_xboole_0(A_135, k4_xboole_0(A_135, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_20])).
% 7.40/2.87  tff(c_4445, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_4405])).
% 7.40/2.87  tff(c_4463, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4445])).
% 7.40/2.87  tff(c_59, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.40/2.87  tff(c_74, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_59, c_14])).
% 7.40/2.87  tff(c_460, plain, (![B_54, A_55]: (k2_xboole_0(k3_xboole_0(B_54, A_55), A_55)=A_55)), inference(resolution, [status(thm)], [c_74, c_211])).
% 7.40/2.87  tff(c_507, plain, (![B_2, B_54]: (k2_xboole_0(B_2, k3_xboole_0(B_54, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_460])).
% 7.40/2.87  tff(c_667, plain, (![A_62, B_63, C_64]: (k2_xboole_0(k2_xboole_0(A_62, B_63), C_64)=k2_xboole_0(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.40/2.87  tff(c_108, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.40/2.87  tff(c_26, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.40/2.87  tff(c_123, plain, (![A_38, B_37]: (r1_tarski(A_38, k2_xboole_0(B_37, A_38)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_26])).
% 7.40/2.87  tff(c_946, plain, (![C_71, A_72, B_73]: (r1_tarski(C_71, k2_xboole_0(A_72, k2_xboole_0(B_73, C_71))))), inference(superposition, [status(thm), theory('equality')], [c_667, c_123])).
% 7.40/2.87  tff(c_1494, plain, (![B_88, B_89, A_90]: (r1_tarski(k3_xboole_0(B_88, B_89), k2_xboole_0(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_507, c_946])).
% 7.40/2.87  tff(c_1545, plain, (![B_88, A_1, B_2]: (r1_tarski(k3_xboole_0(B_88, A_1), k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1494])).
% 7.40/2.87  tff(c_4477, plain, (![B_2]: (r1_tarski('#skF_1', k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), B_2)))), inference(superposition, [status(thm), theory('equality')], [c_4463, c_1545])).
% 7.40/2.87  tff(c_14063, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13618, c_4477])).
% 7.40/2.87  tff(c_14167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_14063])).
% 7.40/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.87  
% 7.40/2.87  Inference rules
% 7.40/2.87  ----------------------
% 7.40/2.87  #Ref     : 0
% 7.40/2.87  #Sup     : 3538
% 7.40/2.87  #Fact    : 0
% 7.40/2.87  #Define  : 0
% 7.40/2.87  #Split   : 0
% 7.40/2.87  #Chain   : 0
% 7.40/2.87  #Close   : 0
% 7.40/2.87  
% 7.40/2.87  Ordering : KBO
% 7.40/2.87  
% 7.40/2.87  Simplification rules
% 7.40/2.87  ----------------------
% 7.40/2.87  #Subsume      : 47
% 7.40/2.87  #Demod        : 3652
% 7.40/2.87  #Tautology    : 2420
% 7.40/2.87  #SimpNegUnit  : 1
% 7.40/2.87  #BackRed      : 1
% 7.40/2.87  
% 7.40/2.87  #Partial instantiations: 0
% 7.40/2.87  #Strategies tried      : 1
% 7.40/2.87  
% 7.40/2.87  Timing (in seconds)
% 7.40/2.87  ----------------------
% 7.40/2.87  Preprocessing        : 0.28
% 7.40/2.87  Parsing              : 0.15
% 7.40/2.87  CNF conversion       : 0.02
% 7.40/2.87  Main loop            : 1.83
% 7.40/2.87  Inferencing          : 0.39
% 7.40/2.87  Reduction            : 1.05
% 7.40/2.87  Demodulation         : 0.93
% 7.40/2.87  BG Simplification    : 0.05
% 7.40/2.87  Subsumption          : 0.25
% 7.40/2.87  Abstraction          : 0.07
% 7.40/2.87  MUC search           : 0.00
% 7.40/2.88  Cooper               : 0.00
% 7.40/2.88  Total                : 2.14
% 7.40/2.88  Index Insertion      : 0.00
% 7.40/2.88  Index Deletion       : 0.00
% 7.40/2.88  Index Matching       : 0.00
% 7.40/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
