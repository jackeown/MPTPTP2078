%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 212 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 315 expanded)
%              Number of equality atoms :   50 ( 140 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_68,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_399,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_xboole_0(A_42,B_43),k4_xboole_0(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_408,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_399])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_468,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_2])).

tff(c_525,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_552,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_525])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_587,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_2')) = k2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_18])).

tff(c_593,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_2,c_587])).

tff(c_90,plain,(
    ! [A_27,B_28] :
      ( r2_xboole_0(A_27,B_28)
      | B_28 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_24])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_122,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_137,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_122])).

tff(c_146,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_2])).

tff(c_200,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_200])).

tff(c_291,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_309,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_3')) = k2_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_291])).

tff(c_323,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2,c_309])).

tff(c_315,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_291])).

tff(c_325,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_315])).

tff(c_360,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_325])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_368,plain,(
    ! [C_41] :
      ( r1_tarski('#skF_1',C_41)
      | ~ r1_tarski('#skF_2',C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_16])).

tff(c_375,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_368])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_375])).

tff(c_381,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_382,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_390,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_382])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_394,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_390,c_14])).

tff(c_480,plain,(
    ! [A_44,B_45] : k2_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_489,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_480])).

tff(c_383,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_76])).

tff(c_492,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_480])).

tff(c_504,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_492])).

tff(c_495,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_480])).

tff(c_498,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_495])).

tff(c_511,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_498])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_414,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_1'),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_22])).

tff(c_439,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_414])).

tff(c_549,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_525])).

tff(c_562,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) = k2_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_18])).

tff(c_568,plain,(
    k2_xboole_0('#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_439,c_2,c_562])).

tff(c_572,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_489])).

tff(c_603,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_572])).

tff(c_621,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_28])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.35  
% 2.69/1.37  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.69/1.37  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.69/1.37  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.69/1.37  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.69/1.37  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.69/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.69/1.37  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.37  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.69/1.37  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.69/1.37  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.37  tff(c_28, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.37  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.37  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.69/1.37  tff(c_68, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.37  tff(c_75, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_68])).
% 2.69/1.37  tff(c_399, plain, (![A_42, B_43]: (k2_xboole_0(k3_xboole_0(A_42, B_43), k4_xboole_0(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.37  tff(c_408, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_75, c_399])).
% 2.69/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.37  tff(c_468, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_408, c_2])).
% 2.69/1.37  tff(c_525, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.37  tff(c_552, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_525])).
% 2.69/1.37  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.37  tff(c_587, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_552, c_18])).
% 2.69/1.37  tff(c_593, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_468, c_2, c_587])).
% 2.69/1.37  tff(c_90, plain, (![A_27, B_28]: (r2_xboole_0(A_27, B_28) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.37  tff(c_24, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.37  tff(c_102, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_24])).
% 2.69/1.37  tff(c_105, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 2.69/1.37  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.37  tff(c_76, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.69/1.37  tff(c_122, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.37  tff(c_137, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_76, c_122])).
% 2.69/1.37  tff(c_146, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_137, c_2])).
% 2.69/1.37  tff(c_200, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.37  tff(c_221, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_76, c_200])).
% 2.69/1.37  tff(c_291, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.37  tff(c_309, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_291])).
% 2.69/1.37  tff(c_323, plain, (k2_xboole_0('#skF_2', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2, c_309])).
% 2.69/1.37  tff(c_315, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_291])).
% 2.69/1.37  tff(c_325, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_315])).
% 2.69/1.37  tff(c_360, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_325])).
% 2.69/1.37  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.37  tff(c_368, plain, (![C_41]: (r1_tarski('#skF_1', C_41) | ~r1_tarski('#skF_2', C_41))), inference(superposition, [status(thm), theory('equality')], [c_360, c_16])).
% 2.69/1.37  tff(c_375, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_368])).
% 2.69/1.37  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_375])).
% 2.69/1.37  tff(c_381, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_102])).
% 2.69/1.37  tff(c_382, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 2.69/1.37  tff(c_390, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_382])).
% 2.69/1.37  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.37  tff(c_394, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_390, c_14])).
% 2.69/1.37  tff(c_480, plain, (![A_44, B_45]: (k2_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.37  tff(c_489, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_394, c_480])).
% 2.69/1.37  tff(c_383, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_381, c_76])).
% 2.69/1.37  tff(c_492, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_383, c_480])).
% 2.69/1.37  tff(c_504, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_492])).
% 2.69/1.37  tff(c_495, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_480])).
% 2.69/1.37  tff(c_498, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_495])).
% 2.69/1.37  tff(c_511, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_498])).
% 2.69/1.37  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.37  tff(c_414, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_383, c_22])).
% 2.69/1.37  tff(c_439, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_414])).
% 2.69/1.37  tff(c_549, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_383, c_525])).
% 2.69/1.37  tff(c_562, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_549, c_18])).
% 2.69/1.37  tff(c_568, plain, (k2_xboole_0('#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_439, c_2, c_562])).
% 2.69/1.37  tff(c_572, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_568, c_489])).
% 2.69/1.37  tff(c_603, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_572])).
% 2.69/1.37  tff(c_621, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_28])).
% 2.69/1.37  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_621])).
% 2.69/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  Inference rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Ref     : 0
% 2.69/1.37  #Sup     : 187
% 2.69/1.37  #Fact    : 0
% 2.69/1.37  #Define  : 0
% 2.69/1.37  #Split   : 1
% 2.69/1.37  #Chain   : 0
% 2.69/1.37  #Close   : 0
% 2.69/1.37  
% 2.69/1.37  Ordering : KBO
% 2.69/1.37  
% 2.69/1.37  Simplification rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Subsume      : 10
% 2.69/1.37  #Demod        : 63
% 2.69/1.37  #Tautology    : 112
% 2.69/1.37  #SimpNegUnit  : 2
% 2.69/1.37  #BackRed      : 23
% 2.69/1.37  
% 2.69/1.37  #Partial instantiations: 0
% 2.69/1.37  #Strategies tried      : 1
% 2.69/1.37  
% 2.69/1.37  Timing (in seconds)
% 2.69/1.37  ----------------------
% 2.69/1.37  Preprocessing        : 0.28
% 2.69/1.37  Parsing              : 0.16
% 2.69/1.37  CNF conversion       : 0.02
% 2.69/1.37  Main loop            : 0.33
% 2.69/1.37  Inferencing          : 0.11
% 2.69/1.37  Reduction            : 0.12
% 2.69/1.37  Demodulation         : 0.09
% 2.69/1.37  BG Simplification    : 0.02
% 2.69/1.37  Subsumption          : 0.05
% 2.69/1.37  Abstraction          : 0.01
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.64
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.37  Index Matching       : 0.00
% 2.69/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
