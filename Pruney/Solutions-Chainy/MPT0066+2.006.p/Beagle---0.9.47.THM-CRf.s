%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 226 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 342 expanded)
%              Number of equality atoms :   50 ( 147 expanded)
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

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

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
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_68,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_122,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_122])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2])).

tff(c_200,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_200])).

tff(c_291,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_306,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_3')) = k2_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_291])).

tff(c_322,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2,c_306])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_318,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_291])).

tff(c_325,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_318])).

tff(c_340,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_325])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_368,plain,(
    ! [C_41] :
      ( r1_tarski('#skF_1',C_41)
      | ~ r1_tarski('#skF_2',C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_16])).

tff(c_375,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_368])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_375])).

tff(c_381,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_383,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_75])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_420,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_1'),k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_22])).

tff(c_474,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_2])).

tff(c_382,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_391,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_382])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_395,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_14])).

tff(c_484,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_502,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_484])).

tff(c_508,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_484])).

tff(c_522,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_508])).

tff(c_400,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_xboole_0(A_42,B_43),k4_xboole_0(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_409,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_400])).

tff(c_437,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_409])).

tff(c_544,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_437])).

tff(c_562,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_574,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_1')) = k2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_562])).

tff(c_590,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_2,c_574])).

tff(c_583,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_562])).

tff(c_621,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_583])).

tff(c_586,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_562])).

tff(c_592,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_586])).

tff(c_622,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_592])).

tff(c_505,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_484])).

tff(c_571,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) = k2_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_562])).

tff(c_589,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_571])).

tff(c_1123,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_622,c_589])).

tff(c_386,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_26])).

tff(c_1143,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_386])).

tff(c_1157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_1143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:54:54 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.49  
% 3.06/1.49  %Foreground sorts:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Background operators:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Foreground operators:
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.49  
% 3.19/1.50  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 3.19/1.50  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.19/1.50  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 3.19/1.50  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.50  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.19/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.19/1.50  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.19/1.50  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.19/1.50  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.19/1.50  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.50  tff(c_90, plain, (![A_27, B_28]: (r2_xboole_0(A_27, B_28) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.19/1.50  tff(c_24, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.19/1.50  tff(c_102, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_24])).
% 3.19/1.50  tff(c_105, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 3.19/1.50  tff(c_26, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.19/1.50  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.19/1.50  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_30])).
% 3.19/1.50  tff(c_68, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.50  tff(c_75, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_68])).
% 3.19/1.50  tff(c_122, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_134, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_75, c_122])).
% 3.19/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.50  tff(c_165, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_134, c_2])).
% 3.19/1.50  tff(c_200, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.50  tff(c_218, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_75, c_200])).
% 3.19/1.50  tff(c_291, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.50  tff(c_306, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_218, c_291])).
% 3.19/1.50  tff(c_322, plain, (k2_xboole_0('#skF_2', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2, c_306])).
% 3.19/1.50  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.19/1.50  tff(c_76, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_68])).
% 3.19/1.50  tff(c_318, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_291])).
% 3.19/1.50  tff(c_325, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_318])).
% 3.19/1.50  tff(c_340, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_325])).
% 3.19/1.50  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.50  tff(c_368, plain, (![C_41]: (r1_tarski('#skF_1', C_41) | ~r1_tarski('#skF_2', C_41))), inference(superposition, [status(thm), theory('equality')], [c_340, c_16])).
% 3.19/1.50  tff(c_375, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_368])).
% 3.19/1.50  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_375])).
% 3.19/1.50  tff(c_381, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_102])).
% 3.19/1.50  tff(c_383, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_381, c_75])).
% 3.19/1.50  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_420, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_383, c_22])).
% 3.19/1.50  tff(c_474, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_420, c_2])).
% 3.19/1.50  tff(c_382, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 3.19/1.50  tff(c_391, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_382])).
% 3.19/1.50  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.50  tff(c_395, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_391, c_14])).
% 3.19/1.50  tff(c_484, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.50  tff(c_502, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_395, c_484])).
% 3.19/1.50  tff(c_508, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_484])).
% 3.19/1.50  tff(c_522, plain, (k3_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_508])).
% 3.19/1.50  tff(c_400, plain, (![A_42, B_43]: (k2_xboole_0(k3_xboole_0(A_42, B_43), k4_xboole_0(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.50  tff(c_409, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_76, c_400])).
% 3.19/1.50  tff(c_437, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2, c_409])).
% 3.19/1.50  tff(c_544, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_522, c_437])).
% 3.19/1.50  tff(c_562, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.50  tff(c_574, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_502, c_562])).
% 3.19/1.50  tff(c_590, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_544, c_2, c_574])).
% 3.19/1.50  tff(c_583, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_383, c_562])).
% 3.19/1.50  tff(c_621, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_583])).
% 3.19/1.50  tff(c_586, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_562])).
% 3.19/1.50  tff(c_592, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_586])).
% 3.19/1.50  tff(c_622, plain, (k2_xboole_0('#skF_2', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_621, c_592])).
% 3.19/1.50  tff(c_505, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_383, c_484])).
% 3.19/1.50  tff(c_571, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_505, c_562])).
% 3.19/1.50  tff(c_589, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_571])).
% 3.19/1.50  tff(c_1123, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_474, c_622, c_589])).
% 3.19/1.50  tff(c_386, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_26])).
% 3.19/1.50  tff(c_1143, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_386])).
% 3.19/1.50  tff(c_1157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_1143])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 337
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 1
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 48
% 3.19/1.50  #Demod        : 133
% 3.19/1.50  #Tautology    : 183
% 3.19/1.50  #SimpNegUnit  : 2
% 3.19/1.50  #BackRed      : 29
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.51  Preprocessing        : 0.28
% 3.19/1.51  Parsing              : 0.16
% 3.19/1.51  CNF conversion       : 0.02
% 3.19/1.51  Main loop            : 0.47
% 3.19/1.51  Inferencing          : 0.16
% 3.19/1.51  Reduction            : 0.17
% 3.19/1.51  Demodulation         : 0.13
% 3.19/1.51  BG Simplification    : 0.02
% 3.19/1.51  Subsumption          : 0.08
% 3.19/1.51  Abstraction          : 0.02
% 3.19/1.51  MUC search           : 0.00
% 3.19/1.51  Cooper               : 0.00
% 3.19/1.51  Total                : 0.79
% 3.19/1.51  Index Insertion      : 0.00
% 3.19/1.51  Index Deletion       : 0.00
% 3.19/1.51  Index Matching       : 0.00
% 3.19/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
