%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 372 expanded)
%              Number of leaves         :   19 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 ( 457 expanded)
%              Number of equality atoms :   48 ( 311 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_91,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_24])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_115,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_100])).

tff(c_121,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_146,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k3_xboole_0(A_30,B_31),C_32) = k3_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [C_32] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_32)) = k4_xboole_0('#skF_1',C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_146])).

tff(c_409,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_474,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_40)) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_409])).

tff(c_571,plain,(
    ! [C_42] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_42)) = k4_xboole_0('#skF_1',C_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_474])).

tff(c_597,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_571])).

tff(c_616,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_72,c_597])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1440,plain,(
    ! [B_53,A_54,C_55] : k4_xboole_0(k3_xboole_0(B_53,A_54),C_55) = k3_xboole_0(A_54,k4_xboole_0(B_53,C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_1594,plain,(
    ! [C_56] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_56)) = k4_xboole_0('#skF_1',C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1440])).

tff(c_1655,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_1',k1_xboole_0)) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1594])).

tff(c_1681,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_118,c_1655])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_590,plain,(
    ! [C_32] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_32)) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_571])).

tff(c_614,plain,(
    ! [C_32] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_32)) = k3_xboole_0('#skF_1',C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_590])).

tff(c_103,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_82,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_82])).

tff(c_483,plain,(
    ! [B_39] : k3_xboole_0('#skF_1',k4_xboole_0(B_39,k3_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_39),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_409])).

tff(c_930,plain,(
    ! [B_47] : k3_xboole_0('#skF_1',k4_xboole_0(B_47,k3_xboole_0('#skF_3','#skF_2'))) = k3_xboole_0('#skF_1',B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_483])).

tff(c_959,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2'))) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_930])).

tff(c_987,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_959])).

tff(c_510,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_40)) = k4_xboole_0('#skF_1',C_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_474])).

tff(c_997,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2'))) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_510])).

tff(c_1010,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_118,c_997])).

tff(c_1554,plain,(
    ! [C_55] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_55)) = k4_xboole_0('#skF_1',C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1440])).

tff(c_2203,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k3_xboole_0(A_60,B_61),k3_xboole_0(B_61,C_62)) = k3_xboole_0(B_61,k4_xboole_0(A_60,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_409])).

tff(c_2383,plain,(
    ! [C_62] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_62)) = k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_2203])).

tff(c_2450,plain,(
    ! [C_63] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_63)) = k4_xboole_0('#skF_1',C_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_2383])).

tff(c_2500,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_2450])).

tff(c_2958,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2500,c_1554])).

tff(c_2974,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_614,c_2958])).

tff(c_2976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2974])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.87  
% 4.63/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.88  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.63/1.88  
% 4.63/1.88  %Foreground sorts:
% 4.63/1.88  
% 4.63/1.88  
% 4.63/1.88  %Background operators:
% 4.63/1.88  
% 4.63/1.88  
% 4.63/1.88  %Foreground operators:
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.63/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/1.88  
% 4.63/1.89  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.63/1.89  tff(f_52, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.63/1.89  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.63/1.89  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.63/1.89  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.63/1.89  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.63/1.89  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.63/1.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.63/1.89  tff(c_91, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.89  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.89  tff(c_99, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_24])).
% 4.63/1.89  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.89  tff(c_100, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.89  tff(c_118, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_100])).
% 4.63/1.89  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.89  tff(c_68, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.89  tff(c_72, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_68])).
% 4.63/1.89  tff(c_115, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_100])).
% 4.63/1.89  tff(c_121, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_115])).
% 4.63/1.89  tff(c_146, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k3_xboole_0(A_30, B_31), C_32)=k3_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.89  tff(c_174, plain, (![C_32]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_32))=k4_xboole_0('#skF_1', C_32))), inference(superposition, [status(thm), theory('equality')], [c_121, c_146])).
% 4.63/1.89  tff(c_409, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40))=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.89  tff(c_474, plain, (![C_40]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_40))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_40)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_409])).
% 4.63/1.89  tff(c_571, plain, (![C_42]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_42))=k4_xboole_0('#skF_1', C_42))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_474])).
% 4.63/1.89  tff(c_597, plain, (k4_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_121, c_571])).
% 4.63/1.89  tff(c_616, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_118, c_72, c_597])).
% 4.63/1.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.89  tff(c_1440, plain, (![B_53, A_54, C_55]: (k4_xboole_0(k3_xboole_0(B_53, A_54), C_55)=k3_xboole_0(A_54, k4_xboole_0(B_53, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 4.63/1.89  tff(c_1594, plain, (![C_56]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_56))=k4_xboole_0('#skF_1', C_56))), inference(superposition, [status(thm), theory('equality')], [c_121, c_1440])).
% 4.63/1.89  tff(c_1655, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', k1_xboole_0))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_118, c_1594])).
% 4.63/1.89  tff(c_1681, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_118, c_1655])).
% 4.63/1.89  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.89  tff(c_590, plain, (![C_32]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_32))=k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_32)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_571])).
% 4.63/1.89  tff(c_614, plain, (![C_32]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_32))=k3_xboole_0('#skF_1', C_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_590])).
% 4.63/1.89  tff(c_103, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, k4_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 4.63/1.89  tff(c_20, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.89  tff(c_25, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 4.63/1.89  tff(c_82, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.89  tff(c_86, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_82])).
% 4.63/1.89  tff(c_483, plain, (![B_39]: (k3_xboole_0('#skF_1', k4_xboole_0(B_39, k3_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0(k3_xboole_0('#skF_1', B_39), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_409])).
% 4.63/1.89  tff(c_930, plain, (![B_47]: (k3_xboole_0('#skF_1', k4_xboole_0(B_47, k3_xboole_0('#skF_3', '#skF_2')))=k3_xboole_0('#skF_1', B_47))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_483])).
% 4.63/1.89  tff(c_959, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2')))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_103, c_930])).
% 4.63/1.89  tff(c_987, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_959])).
% 4.63/1.89  tff(c_510, plain, (![C_40]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_40))=k4_xboole_0('#skF_1', C_40))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_474])).
% 4.63/1.89  tff(c_997, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2')))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_987, c_510])).
% 4.63/1.89  tff(c_1010, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_616, c_118, c_997])).
% 4.63/1.89  tff(c_1554, plain, (![C_55]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_55))=k4_xboole_0('#skF_1', C_55))), inference(superposition, [status(thm), theory('equality')], [c_121, c_1440])).
% 4.63/1.89  tff(c_2203, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k3_xboole_0(A_60, B_61), k3_xboole_0(B_61, C_62))=k3_xboole_0(B_61, k4_xboole_0(A_60, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_409])).
% 4.63/1.89  tff(c_2383, plain, (![C_62]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_62))=k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_62)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_2203])).
% 4.63/1.89  tff(c_2450, plain, (![C_63]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_63))=k4_xboole_0('#skF_1', C_63))), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_2383])).
% 4.63/1.89  tff(c_2500, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1010, c_2450])).
% 4.63/1.89  tff(c_2958, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2500, c_1554])).
% 4.63/1.89  tff(c_2974, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_614, c_2958])).
% 4.63/1.89  tff(c_2976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2974])).
% 4.63/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.89  
% 4.63/1.89  Inference rules
% 4.63/1.89  ----------------------
% 4.63/1.89  #Ref     : 0
% 4.63/1.89  #Sup     : 750
% 4.63/1.89  #Fact    : 0
% 4.63/1.89  #Define  : 0
% 4.63/1.89  #Split   : 0
% 4.63/1.89  #Chain   : 0
% 4.63/1.89  #Close   : 0
% 4.63/1.89  
% 4.63/1.89  Ordering : KBO
% 4.63/1.89  
% 4.63/1.89  Simplification rules
% 4.63/1.89  ----------------------
% 4.63/1.89  #Subsume      : 12
% 4.63/1.89  #Demod        : 788
% 4.63/1.89  #Tautology    : 403
% 4.63/1.89  #SimpNegUnit  : 1
% 4.63/1.89  #BackRed      : 6
% 4.63/1.89  
% 4.63/1.89  #Partial instantiations: 0
% 4.63/1.89  #Strategies tried      : 1
% 4.63/1.89  
% 4.63/1.89  Timing (in seconds)
% 4.63/1.89  ----------------------
% 4.63/1.89  Preprocessing        : 0.29
% 4.63/1.89  Parsing              : 0.15
% 4.63/1.89  CNF conversion       : 0.02
% 4.63/1.89  Main loop            : 0.84
% 4.63/1.89  Inferencing          : 0.24
% 4.63/1.89  Reduction            : 0.41
% 4.63/1.89  Demodulation         : 0.35
% 4.63/1.89  BG Simplification    : 0.03
% 4.63/1.89  Subsumption          : 0.11
% 4.63/1.89  Abstraction          : 0.04
% 4.63/1.89  MUC search           : 0.00
% 4.63/1.89  Cooper               : 0.00
% 4.63/1.89  Total                : 1.16
% 4.63/1.89  Index Insertion      : 0.00
% 4.63/1.89  Index Deletion       : 0.00
% 4.63/1.89  Index Matching       : 0.00
% 4.63/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
