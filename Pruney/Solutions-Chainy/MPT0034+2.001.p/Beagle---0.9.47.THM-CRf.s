%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 29.68s
% Output     : CNFRefutation 29.68s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 390 expanded)
%              Number of leaves         :   19 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 439 expanded)
%              Number of equality atoms :   43 ( 299 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_249,plain,(
    ! [A_36,B_37] : k2_xboole_0(k3_xboole_0(A_36,B_37),A_36) = A_36 ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_277,plain,(
    ! [A_1,B_37] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_37)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_427,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k2_xboole_0(A_48,B_49),k2_xboole_0(A_48,C_50)) = k2_xboole_0(A_48,k3_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_508,plain,(
    ! [A_3,C_50] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_50)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_427])).

tff(c_520,plain,(
    ! [A_51,C_52] : k3_xboole_0(A_51,k2_xboole_0(A_51,C_52)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_508])).

tff(c_17355,plain,(
    ! [A_270,B_271] : k3_xboole_0(k3_xboole_0(A_270,B_271),A_270) = k3_xboole_0(A_270,B_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_520])).

tff(c_17691,plain,(
    ! [C_9,B_8] : k3_xboole_0(C_9,k3_xboole_0(B_8,C_9)) = k3_xboole_0(C_9,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_17355])).

tff(c_560,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_520])).

tff(c_16,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_39])).

tff(c_134,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_140,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2])).

tff(c_469,plain,(
    ! [A_31,B_49] : k3_xboole_0(k2_xboole_0(A_31,B_49),A_31) = k2_xboole_0(A_31,k3_xboole_0(B_49,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_427])).

tff(c_516,plain,(
    ! [A_31,B_49] : k3_xboole_0(k2_xboole_0(A_31,B_49),A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_16,c_469])).

tff(c_511,plain,(
    ! [A_3,B_49] : k3_xboole_0(k2_xboole_0(A_3,B_49),A_3) = k2_xboole_0(A_3,k3_xboole_0(B_49,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_427])).

tff(c_2203,plain,(
    ! [A_87,B_88] : k2_xboole_0(A_87,k3_xboole_0(B_88,A_87)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_511])).

tff(c_1275,plain,(
    ! [A_69,B_70] : k3_xboole_0(k2_xboole_0(A_69,B_70),A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_16,c_469])).

tff(c_1349,plain,(
    ! [B_2,A_1] : k3_xboole_0(k2_xboole_0(B_2,A_1),A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1275])).

tff(c_45829,plain,(
    ! [A_417,B_418] : k3_xboole_0(A_417,k3_xboole_0(B_418,A_417)) = k3_xboole_0(B_418,A_417) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_1349])).

tff(c_2217,plain,(
    ! [A_87,B_88] : k3_xboole_0(A_87,k3_xboole_0(B_88,A_87)) = k3_xboole_0(B_88,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_1349])).

tff(c_45832,plain,(
    ! [B_418,A_417] : k3_xboole_0(k3_xboole_0(B_418,A_417),k3_xboole_0(B_418,A_417)) = k3_xboole_0(A_417,k3_xboole_0(B_418,A_417)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45829,c_2217])).

tff(c_46553,plain,(
    ! [B_418,A_417] : k3_xboole_0(B_418,A_417) = k3_xboole_0(A_417,B_418) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17691,c_560,c_45832])).

tff(c_18,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_47619,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46553,c_18])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_5168,plain,(
    ! [A_128,B_129,C_130,C_131] : k3_xboole_0(k2_xboole_0(A_128,B_129),k3_xboole_0(k2_xboole_0(A_128,C_130),C_131)) = k3_xboole_0(k2_xboole_0(A_128,k3_xboole_0(B_129,C_130)),C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_8])).

tff(c_6443,plain,(
    ! [C_149,C_150] : k3_xboole_0(k2_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_149)),C_150) = k3_xboole_0('#skF_2',k3_xboole_0(k2_xboole_0('#skF_1',C_149),C_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_5168])).

tff(c_6682,plain,(
    ! [C_150] : k3_xboole_0('#skF_2',k3_xboole_0(k2_xboole_0('#skF_1',k1_xboole_0),C_150)) = k3_xboole_0(k2_xboole_0('#skF_1',k1_xboole_0),C_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6443])).

tff(c_6720,plain,(
    ! [C_150] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',C_150)) = k3_xboole_0('#skF_1',C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_6682])).

tff(c_17573,plain,(
    ! [C_150] : k3_xboole_0(k3_xboole_0('#skF_1',C_150),'#skF_2') = k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',C_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6720,c_17355])).

tff(c_17757,plain,(
    ! [C_150] : k3_xboole_0('#skF_1',k3_xboole_0(C_150,'#skF_2')) = k3_xboole_0('#skF_1',C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6720,c_8,c_17573])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_92,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_5398,plain,(
    ! [A_3,C_130,C_131] : k3_xboole_0(k2_xboole_0(A_3,k3_xboole_0(A_3,C_130)),C_131) = k3_xboole_0(A_3,k3_xboole_0(k2_xboole_0(A_3,C_130),C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5168])).

tff(c_10013,plain,(
    ! [A_204,C_205,C_206] : k3_xboole_0(A_204,k3_xboole_0(k2_xboole_0(A_204,C_205),C_206)) = k3_xboole_0(A_204,C_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_5398])).

tff(c_11555,plain,(
    ! [C_221] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_221)) = k3_xboole_0('#skF_3',C_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10013])).

tff(c_1495,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_10])).

tff(c_1541,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1495])).

tff(c_2363,plain,(
    ! [B_89,A_90] : r1_tarski(k3_xboole_0(B_89,A_90),A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_1541])).

tff(c_2427,plain,(
    ! [A_7,B_8,C_9] : r1_tarski(k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)),C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2363])).

tff(c_110471,plain,(
    ! [A_625,C_626] : r1_tarski(k3_xboole_0(A_625,k3_xboole_0('#skF_3',C_626)),k3_xboole_0('#skF_4',C_626)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11555,c_2427])).

tff(c_110692,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17757,c_110471])).

tff(c_110897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47619,c_110692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:26:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.68/21.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.68/21.54  
% 29.68/21.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.68/21.54  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 29.68/21.54  
% 29.68/21.54  %Foreground sorts:
% 29.68/21.54  
% 29.68/21.54  
% 29.68/21.54  %Background operators:
% 29.68/21.54  
% 29.68/21.54  
% 29.68/21.54  %Foreground operators:
% 29.68/21.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.68/21.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.68/21.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.68/21.54  tff('#skF_2', type, '#skF_2': $i).
% 29.68/21.54  tff('#skF_3', type, '#skF_3': $i).
% 29.68/21.54  tff('#skF_1', type, '#skF_1': $i).
% 29.68/21.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.68/21.54  tff('#skF_4', type, '#skF_4': $i).
% 29.68/21.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.68/21.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.68/21.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.68/21.54  
% 29.68/21.56  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 29.68/21.56  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 29.68/21.56  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 29.68/21.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 29.68/21.56  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 29.68/21.56  tff(f_45, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 29.68/21.56  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 29.68/21.56  tff(f_54, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 29.68/21.56  tff(c_8, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.68/21.56  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.68/21.56  tff(c_77, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.68/21.56  tff(c_91, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_10, c_77])).
% 29.68/21.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.68/21.56  tff(c_249, plain, (![A_36, B_37]: (k2_xboole_0(k3_xboole_0(A_36, B_37), A_36)=A_36)), inference(resolution, [status(thm)], [c_10, c_77])).
% 29.68/21.56  tff(c_277, plain, (![A_1, B_37]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_37))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 29.68/21.56  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.68/21.56  tff(c_427, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k2_xboole_0(A_48, B_49), k2_xboole_0(A_48, C_50))=k2_xboole_0(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.68/21.56  tff(c_508, plain, (![A_3, C_50]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_50))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_427])).
% 29.68/21.56  tff(c_520, plain, (![A_51, C_52]: (k3_xboole_0(A_51, k2_xboole_0(A_51, C_52))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_277, c_508])).
% 29.68/21.56  tff(c_17355, plain, (![A_270, B_271]: (k3_xboole_0(k3_xboole_0(A_270, B_271), A_270)=k3_xboole_0(A_270, B_271))), inference(superposition, [status(thm), theory('equality')], [c_91, c_520])).
% 29.68/21.56  tff(c_17691, plain, (![C_9, B_8]: (k3_xboole_0(C_9, k3_xboole_0(B_8, C_9))=k3_xboole_0(C_9, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_17355])).
% 29.68/21.56  tff(c_560, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_277, c_520])).
% 29.68/21.56  tff(c_16, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.68/21.56  tff(c_39, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.68/21.56  tff(c_42, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_39])).
% 29.68/21.56  tff(c_134, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(resolution, [status(thm)], [c_42, c_77])).
% 29.68/21.56  tff(c_140, plain, (![A_31]: (k2_xboole_0(A_31, k1_xboole_0)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_134, c_2])).
% 29.68/21.56  tff(c_469, plain, (![A_31, B_49]: (k3_xboole_0(k2_xboole_0(A_31, B_49), A_31)=k2_xboole_0(A_31, k3_xboole_0(B_49, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_427])).
% 29.68/21.56  tff(c_516, plain, (![A_31, B_49]: (k3_xboole_0(k2_xboole_0(A_31, B_49), A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_16, c_469])).
% 29.68/21.56  tff(c_511, plain, (![A_3, B_49]: (k3_xboole_0(k2_xboole_0(A_3, B_49), A_3)=k2_xboole_0(A_3, k3_xboole_0(B_49, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_427])).
% 29.68/21.56  tff(c_2203, plain, (![A_87, B_88]: (k2_xboole_0(A_87, k3_xboole_0(B_88, A_87))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_516, c_511])).
% 29.68/21.56  tff(c_1275, plain, (![A_69, B_70]: (k3_xboole_0(k2_xboole_0(A_69, B_70), A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_16, c_469])).
% 29.68/21.56  tff(c_1349, plain, (![B_2, A_1]: (k3_xboole_0(k2_xboole_0(B_2, A_1), A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1275])).
% 29.68/21.56  tff(c_45829, plain, (![A_417, B_418]: (k3_xboole_0(A_417, k3_xboole_0(B_418, A_417))=k3_xboole_0(B_418, A_417))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_1349])).
% 29.68/21.56  tff(c_2217, plain, (![A_87, B_88]: (k3_xboole_0(A_87, k3_xboole_0(B_88, A_87))=k3_xboole_0(B_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_1349])).
% 29.68/21.56  tff(c_45832, plain, (![B_418, A_417]: (k3_xboole_0(k3_xboole_0(B_418, A_417), k3_xboole_0(B_418, A_417))=k3_xboole_0(A_417, k3_xboole_0(B_418, A_417)))), inference(superposition, [status(thm), theory('equality')], [c_45829, c_2217])).
% 29.68/21.56  tff(c_46553, plain, (![B_418, A_417]: (k3_xboole_0(B_418, A_417)=k3_xboole_0(A_417, B_418))), inference(demodulation, [status(thm), theory('equality')], [c_17691, c_560, c_45832])).
% 29.68/21.56  tff(c_18, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.68/21.56  tff(c_47619, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46553, c_18])).
% 29.68/21.56  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.68/21.56  tff(c_93, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_77])).
% 29.68/21.56  tff(c_5168, plain, (![A_128, B_129, C_130, C_131]: (k3_xboole_0(k2_xboole_0(A_128, B_129), k3_xboole_0(k2_xboole_0(A_128, C_130), C_131))=k3_xboole_0(k2_xboole_0(A_128, k3_xboole_0(B_129, C_130)), C_131))), inference(superposition, [status(thm), theory('equality')], [c_427, c_8])).
% 29.68/21.56  tff(c_6443, plain, (![C_149, C_150]: (k3_xboole_0(k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_149)), C_150)=k3_xboole_0('#skF_2', k3_xboole_0(k2_xboole_0('#skF_1', C_149), C_150)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_5168])).
% 29.68/21.56  tff(c_6682, plain, (![C_150]: (k3_xboole_0('#skF_2', k3_xboole_0(k2_xboole_0('#skF_1', k1_xboole_0), C_150))=k3_xboole_0(k2_xboole_0('#skF_1', k1_xboole_0), C_150))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6443])).
% 29.68/21.56  tff(c_6720, plain, (![C_150]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', C_150))=k3_xboole_0('#skF_1', C_150))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_6682])).
% 29.68/21.56  tff(c_17573, plain, (![C_150]: (k3_xboole_0(k3_xboole_0('#skF_1', C_150), '#skF_2')=k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', C_150)))), inference(superposition, [status(thm), theory('equality')], [c_6720, c_17355])).
% 29.68/21.56  tff(c_17757, plain, (![C_150]: (k3_xboole_0('#skF_1', k3_xboole_0(C_150, '#skF_2'))=k3_xboole_0('#skF_1', C_150))), inference(demodulation, [status(thm), theory('equality')], [c_6720, c_8, c_17573])).
% 29.68/21.56  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.68/21.56  tff(c_92, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_77])).
% 29.68/21.56  tff(c_5398, plain, (![A_3, C_130, C_131]: (k3_xboole_0(k2_xboole_0(A_3, k3_xboole_0(A_3, C_130)), C_131)=k3_xboole_0(A_3, k3_xboole_0(k2_xboole_0(A_3, C_130), C_131)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5168])).
% 29.68/21.56  tff(c_10013, plain, (![A_204, C_205, C_206]: (k3_xboole_0(A_204, k3_xboole_0(k2_xboole_0(A_204, C_205), C_206))=k3_xboole_0(A_204, C_206))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_5398])).
% 29.68/21.56  tff(c_11555, plain, (![C_221]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_221))=k3_xboole_0('#skF_3', C_221))), inference(superposition, [status(thm), theory('equality')], [c_92, c_10013])).
% 29.68/21.56  tff(c_1495, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_1275, c_10])).
% 29.68/21.56  tff(c_1541, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1495])).
% 29.68/21.56  tff(c_2363, plain, (![B_89, A_90]: (r1_tarski(k3_xboole_0(B_89, A_90), A_90))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_1541])).
% 29.68/21.56  tff(c_2427, plain, (![A_7, B_8, C_9]: (r1_tarski(k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)), C_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2363])).
% 29.68/21.56  tff(c_110471, plain, (![A_625, C_626]: (r1_tarski(k3_xboole_0(A_625, k3_xboole_0('#skF_3', C_626)), k3_xboole_0('#skF_4', C_626)))), inference(superposition, [status(thm), theory('equality')], [c_11555, c_2427])).
% 29.68/21.56  tff(c_110692, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17757, c_110471])).
% 29.68/21.56  tff(c_110897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47619, c_110692])).
% 29.68/21.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.68/21.56  
% 29.68/21.56  Inference rules
% 29.68/21.56  ----------------------
% 29.68/21.56  #Ref     : 0
% 29.68/21.56  #Sup     : 27660
% 29.68/21.56  #Fact    : 0
% 29.68/21.56  #Define  : 0
% 29.68/21.56  #Split   : 2
% 29.68/21.56  #Chain   : 0
% 29.68/21.56  #Close   : 0
% 29.68/21.56  
% 29.68/21.56  Ordering : KBO
% 29.68/21.56  
% 29.68/21.56  Simplification rules
% 29.68/21.56  ----------------------
% 29.68/21.56  #Subsume      : 894
% 29.68/21.56  #Demod        : 30396
% 29.68/21.56  #Tautology    : 14988
% 29.68/21.56  #SimpNegUnit  : 1
% 29.68/21.56  #BackRed      : 6
% 29.68/21.56  
% 29.68/21.56  #Partial instantiations: 0
% 29.68/21.56  #Strategies tried      : 1
% 29.68/21.56  
% 29.68/21.56  Timing (in seconds)
% 29.68/21.56  ----------------------
% 29.68/21.56  Preprocessing        : 0.24
% 29.68/21.56  Parsing              : 0.13
% 29.68/21.56  CNF conversion       : 0.02
% 29.68/21.56  Main loop            : 20.61
% 29.68/21.56  Inferencing          : 1.74
% 29.68/21.56  Reduction            : 14.36
% 29.68/21.56  Demodulation         : 13.51
% 29.68/21.56  BG Simplification    : 0.28
% 29.68/21.56  Subsumption          : 3.55
% 29.68/21.56  Abstraction          : 0.42
% 29.68/21.56  MUC search           : 0.00
% 29.68/21.56  Cooper               : 0.00
% 29.68/21.56  Total                : 20.88
% 29.68/21.56  Index Insertion      : 0.00
% 29.68/21.56  Index Deletion       : 0.00
% 29.68/21.56  Index Matching       : 0.00
% 29.68/21.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
