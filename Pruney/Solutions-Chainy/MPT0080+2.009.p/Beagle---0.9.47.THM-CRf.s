%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 458 expanded)
%              Number of leaves         :   22 ( 165 expanded)
%              Depth                    :   17
%              Number of atoms          :   72 ( 482 expanded)
%              Number of equality atoms :   56 ( 410 expanded)
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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_34,B_35] : k4_xboole_0(k2_xboole_0(A_34,B_35),B_35) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_34] : k4_xboole_0(A_34,k1_xboole_0) = k2_xboole_0(A_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_14])).

tff(c_183,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_140,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_288,plain,(
    ! [A_40,B_41] : k2_xboole_0(k3_xboole_0(A_40,B_41),A_40) = A_40 ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_332,plain,(
    ! [B_42] : k3_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_183])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_343,plain,(
    ! [B_42] : k3_xboole_0(B_42,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_4])).

tff(c_266,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_284,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_266])).

tff(c_483,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_284])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_651,plain,(
    ! [A_54,B_55] : k4_xboole_0(k2_xboole_0(A_54,B_55),A_54) = k4_xboole_0(B_55,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_689,plain,(
    ! [A_34] : k4_xboole_0(k1_xboole_0,A_34) = k4_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_651])).

tff(c_715,plain,(
    ! [A_34] : k4_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_689])).

tff(c_485,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_284])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_490,plain,(
    ! [A_48,C_16] : k4_xboole_0(A_48,k2_xboole_0(A_48,C_16)) = k4_xboole_0(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_18])).

tff(c_1421,plain,(
    ! [A_48,C_16] : k4_xboole_0(A_48,k2_xboole_0(A_48,C_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_490])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1060,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,k4_xboole_0(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_20])).

tff(c_1100,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1060])).

tff(c_1116,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1100])).

tff(c_766,plain,(
    ! [B_57,A_58] : k2_xboole_0(k3_xboole_0(B_57,A_58),A_58) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_288])).

tff(c_820,plain,(
    ! [A_1,B_57] : k2_xboole_0(A_1,k3_xboole_0(B_57,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_766])).

tff(c_1126,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_820])).

tff(c_1423,plain,(
    ! [A_71,C_72] : k4_xboole_0(A_71,k2_xboole_0(A_71,C_72)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_490])).

tff(c_1444,plain,(
    ! [A_71,C_72] : k3_xboole_0(A_71,k2_xboole_0(A_71,C_72)) = k4_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_20])).

tff(c_1512,plain,(
    ! [A_73,C_74] : k3_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1444])).

tff(c_1586,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1512])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_281,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = k3_xboole_0(k2_xboole_0(A_12,B_13),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_266])).

tff(c_287,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = k3_xboole_0(B_13,k2_xboole_0(A_12,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_281])).

tff(c_3060,plain,(
    ! [A_103,B_104] : k4_xboole_0(k2_xboole_0(A_103,B_104),k4_xboole_0(A_103,B_104)) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_287])).

tff(c_3117,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_3060])).

tff(c_3200,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_1421,c_18,c_2,c_18,c_3117])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_160,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_27,c_140])).

tff(c_257,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_16])).

tff(c_484,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_257])).

tff(c_427,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k4_xboole_0(A_45,B_46),C_47) = k4_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_440,plain,(
    ! [A_45,B_46,B_18] : k4_xboole_0(A_45,k2_xboole_0(B_46,k4_xboole_0(k4_xboole_0(A_45,B_46),B_18))) = k3_xboole_0(k4_xboole_0(A_45,B_46),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_20])).

tff(c_3589,plain,(
    ! [A_110,B_111,B_112] : k4_xboole_0(A_110,k2_xboole_0(B_111,k4_xboole_0(A_110,k2_xboole_0(B_111,B_112)))) = k3_xboole_0(k4_xboole_0(A_110,B_111),B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_440])).

tff(c_3743,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_3589])).

tff(c_3820,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_4,c_3200,c_183,c_4,c_3743])).

tff(c_38,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_22,A_23] : r1_tarski(k3_xboole_0(B_22,A_23),A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_3874,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_53])).

tff(c_3890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_3874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.78  
% 4.17/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.79  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.17/1.79  
% 4.17/1.79  %Foreground sorts:
% 4.17/1.79  
% 4.17/1.79  
% 4.17/1.79  %Background operators:
% 4.17/1.79  
% 4.17/1.79  
% 4.17/1.79  %Foreground operators:
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.17/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.17/1.79  
% 4.17/1.80  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.17/1.80  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.17/1.80  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.17/1.80  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.17/1.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.17/1.80  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.17/1.80  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.17/1.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.17/1.80  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.17/1.80  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.17/1.80  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.17/1.80  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.17/1.80  tff(c_161, plain, (![A_34, B_35]: (k4_xboole_0(k2_xboole_0(A_34, B_35), B_35)=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.17/1.80  tff(c_168, plain, (![A_34]: (k4_xboole_0(A_34, k1_xboole_0)=k2_xboole_0(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_14])).
% 4.17/1.80  tff(c_183, plain, (![A_34]: (k2_xboole_0(A_34, k1_xboole_0)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_168])).
% 4.17/1.80  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.17/1.80  tff(c_140, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.17/1.80  tff(c_288, plain, (![A_40, B_41]: (k2_xboole_0(k3_xboole_0(A_40, B_41), A_40)=A_40)), inference(resolution, [status(thm)], [c_12, c_140])).
% 4.17/1.80  tff(c_332, plain, (![B_42]: (k3_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_288, c_183])).
% 4.17/1.80  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.17/1.80  tff(c_343, plain, (![B_42]: (k3_xboole_0(B_42, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_332, c_4])).
% 4.17/1.80  tff(c_266, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.17/1.80  tff(c_284, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_266])).
% 4.17/1.80  tff(c_483, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_284])).
% 4.17/1.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.17/1.80  tff(c_651, plain, (![A_54, B_55]: (k4_xboole_0(k2_xboole_0(A_54, B_55), A_54)=k4_xboole_0(B_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 4.17/1.80  tff(c_689, plain, (![A_34]: (k4_xboole_0(k1_xboole_0, A_34)=k4_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_183, c_651])).
% 4.17/1.80  tff(c_715, plain, (![A_34]: (k4_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_483, c_689])).
% 4.17/1.80  tff(c_485, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_284])).
% 4.17/1.80  tff(c_18, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.17/1.80  tff(c_490, plain, (![A_48, C_16]: (k4_xboole_0(A_48, k2_xboole_0(A_48, C_16))=k4_xboole_0(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_485, c_18])).
% 4.17/1.80  tff(c_1421, plain, (![A_48, C_16]: (k4_xboole_0(A_48, k2_xboole_0(A_48, C_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_490])).
% 4.17/1.80  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.17/1.80  tff(c_121, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.17/1.80  tff(c_129, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_121])).
% 4.17/1.80  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.17/1.80  tff(c_1060, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k3_xboole_0(A_66, k4_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_266, c_20])).
% 4.17/1.80  tff(c_1100, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_129, c_1060])).
% 4.17/1.80  tff(c_1116, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1100])).
% 4.17/1.80  tff(c_766, plain, (![B_57, A_58]: (k2_xboole_0(k3_xboole_0(B_57, A_58), A_58)=A_58)), inference(superposition, [status(thm), theory('equality')], [c_4, c_288])).
% 4.17/1.80  tff(c_820, plain, (![A_1, B_57]: (k2_xboole_0(A_1, k3_xboole_0(B_57, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_766])).
% 4.17/1.80  tff(c_1126, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1116, c_820])).
% 4.17/1.80  tff(c_1423, plain, (![A_71, C_72]: (k4_xboole_0(A_71, k2_xboole_0(A_71, C_72))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_490])).
% 4.17/1.80  tff(c_1444, plain, (![A_71, C_72]: (k3_xboole_0(A_71, k2_xboole_0(A_71, C_72))=k4_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_20])).
% 4.17/1.80  tff(c_1512, plain, (![A_73, C_74]: (k3_xboole_0(A_73, k2_xboole_0(A_73, C_74))=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1444])).
% 4.17/1.80  tff(c_1586, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1512])).
% 4.17/1.80  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.17/1.80  tff(c_281, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=k3_xboole_0(k2_xboole_0(A_12, B_13), B_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_266])).
% 4.17/1.80  tff(c_287, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=k3_xboole_0(B_13, k2_xboole_0(A_12, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_281])).
% 4.17/1.80  tff(c_3060, plain, (![A_103, B_104]: (k4_xboole_0(k2_xboole_0(A_103, B_104), k4_xboole_0(A_103, B_104))=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_287])).
% 4.17/1.80  tff(c_3117, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1126, c_3060])).
% 4.17/1.80  tff(c_3200, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_1421, c_18, c_2, c_18, c_3117])).
% 4.17/1.80  tff(c_26, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.17/1.80  tff(c_27, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 4.17/1.80  tff(c_160, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_27, c_140])).
% 4.17/1.80  tff(c_257, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_16])).
% 4.17/1.80  tff(c_484, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_483, c_257])).
% 4.17/1.80  tff(c_427, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k4_xboole_0(A_45, B_46), C_47)=k4_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.17/1.80  tff(c_440, plain, (![A_45, B_46, B_18]: (k4_xboole_0(A_45, k2_xboole_0(B_46, k4_xboole_0(k4_xboole_0(A_45, B_46), B_18)))=k3_xboole_0(k4_xboole_0(A_45, B_46), B_18))), inference(superposition, [status(thm), theory('equality')], [c_427, c_20])).
% 4.17/1.80  tff(c_3589, plain, (![A_110, B_111, B_112]: (k4_xboole_0(A_110, k2_xboole_0(B_111, k4_xboole_0(A_110, k2_xboole_0(B_111, B_112))))=k3_xboole_0(k4_xboole_0(A_110, B_111), B_112))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_440])).
% 4.17/1.80  tff(c_3743, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_484, c_3589])).
% 4.17/1.80  tff(c_3820, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3200, c_4, c_3200, c_183, c_4, c_3743])).
% 4.17/1.80  tff(c_38, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.17/1.80  tff(c_53, plain, (![B_22, A_23]: (r1_tarski(k3_xboole_0(B_22, A_23), A_23))), inference(superposition, [status(thm), theory('equality')], [c_38, c_12])).
% 4.17/1.80  tff(c_3874, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3820, c_53])).
% 4.17/1.80  tff(c_3890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_3874])).
% 4.17/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.80  
% 4.17/1.80  Inference rules
% 4.17/1.80  ----------------------
% 4.17/1.80  #Ref     : 0
% 4.17/1.80  #Sup     : 963
% 4.17/1.80  #Fact    : 0
% 4.17/1.80  #Define  : 0
% 4.17/1.80  #Split   : 0
% 4.17/1.80  #Chain   : 0
% 4.17/1.80  #Close   : 0
% 4.17/1.80  
% 4.17/1.80  Ordering : KBO
% 4.17/1.80  
% 4.17/1.80  Simplification rules
% 4.17/1.80  ----------------------
% 4.17/1.80  #Subsume      : 0
% 4.17/1.80  #Demod        : 897
% 4.17/1.80  #Tautology    : 699
% 4.17/1.80  #SimpNegUnit  : 1
% 4.17/1.80  #BackRed      : 7
% 4.17/1.80  
% 4.17/1.80  #Partial instantiations: 0
% 4.17/1.80  #Strategies tried      : 1
% 4.17/1.80  
% 4.17/1.80  Timing (in seconds)
% 4.17/1.80  ----------------------
% 4.17/1.81  Preprocessing        : 0.28
% 4.17/1.81  Parsing              : 0.16
% 4.17/1.81  CNF conversion       : 0.02
% 4.17/1.81  Main loop            : 0.71
% 4.17/1.81  Inferencing          : 0.21
% 4.17/1.81  Reduction            : 0.35
% 4.17/1.81  Demodulation         : 0.30
% 4.17/1.81  BG Simplification    : 0.02
% 4.17/1.81  Subsumption          : 0.09
% 4.17/1.81  Abstraction          : 0.03
% 4.17/1.81  MUC search           : 0.00
% 4.17/1.81  Cooper               : 0.00
% 4.17/1.81  Total                : 1.03
% 4.17/1.81  Index Insertion      : 0.00
% 4.17/1.81  Index Deletion       : 0.00
% 4.17/1.81  Index Matching       : 0.00
% 4.17/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
