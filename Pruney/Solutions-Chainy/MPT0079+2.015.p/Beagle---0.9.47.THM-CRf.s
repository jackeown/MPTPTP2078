%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 143 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 150 expanded)
%              Number of equality atoms :   57 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_615,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_437,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_475,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_437])).

tff(c_484,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_475])).

tff(c_625,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(B_47,k4_xboole_0(A_46,B_47))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_484])).

tff(c_684,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(B_47,A_46)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_231,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_231])).

tff(c_297,plain,(
    ! [A_37,B_38] : k2_xboole_0(k3_xboole_0(A_37,B_38),k4_xboole_0(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_309,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_297])).

tff(c_146,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_162,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_10])).

tff(c_335,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_162])).

tff(c_9298,plain,(
    ! [C_147] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_147)) = k4_xboole_0('#skF_3',C_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_615])).

tff(c_9423,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_9298])).

tff(c_9455,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_9423])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1434,plain,(
    ! [A_66,B_67] : k2_xboole_0(k3_xboole_0(A_66,B_67),k4_xboole_0(B_67,A_66)) = B_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_297])).

tff(c_1520,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_1434])).

tff(c_1574,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_162])).

tff(c_696,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_747,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_696])).

tff(c_9534,plain,(
    ! [C_148,A_149,B_150] : k2_xboole_0(C_148,k4_xboole_0(A_149,k2_xboole_0(B_150,C_148))) = k2_xboole_0(C_148,k4_xboole_0(A_149,B_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_14])).

tff(c_9783,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_9534])).

tff(c_9889,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_10,c_9783])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_708,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = k4_xboole_0(A_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_22])).

tff(c_753,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_708])).

tff(c_1001,plain,(
    ! [A_57,C_58,B_59] : k2_xboole_0(k4_xboole_0(A_57,C_58),k4_xboole_0(B_59,C_58)) = k4_xboole_0(k2_xboole_0(A_57,B_59),C_58) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1072,plain,(
    ! [A_57,A_11] : k4_xboole_0(k2_xboole_0(A_57,A_11),A_11) = k2_xboole_0(k4_xboole_0(A_57,A_11),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_1001])).

tff(c_2025,plain,(
    ! [A_76,A_77] : k4_xboole_0(k2_xboole_0(A_76,A_77),A_77) = k4_xboole_0(A_76,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1072])).

tff(c_2053,plain,(
    ! [A_76,A_77] : k4_xboole_0(k2_xboole_0(A_76,A_77),k4_xboole_0(A_76,A_77)) = k3_xboole_0(k2_xboole_0(A_76,A_77),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_22])).

tff(c_2120,plain,(
    ! [A_76,A_77] : k4_xboole_0(k2_xboole_0(A_76,A_77),k4_xboole_0(A_76,A_77)) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_4,c_2053])).

tff(c_9935,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9889,c_2120])).

tff(c_9979,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_9455,c_9935])).

tff(c_9981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_9979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.73  
% 6.29/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.73  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.52/2.73  
% 6.52/2.73  %Foreground sorts:
% 6.52/2.73  
% 6.52/2.73  
% 6.52/2.73  %Background operators:
% 6.52/2.73  
% 6.52/2.73  
% 6.52/2.73  %Foreground operators:
% 6.52/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.52/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.52/2.73  tff('#skF_2', type, '#skF_2': $i).
% 6.52/2.73  tff('#skF_3', type, '#skF_3': $i).
% 6.52/2.73  tff('#skF_1', type, '#skF_1': $i).
% 6.52/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.73  tff('#skF_4', type, '#skF_4': $i).
% 6.52/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.52/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.52/2.73  
% 6.52/2.75  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.52/2.75  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.52/2.75  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.52/2.75  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.52/2.75  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.52/2.75  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.52/2.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.52/2.75  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.52/2.75  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.52/2.75  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.52/2.75  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.52/2.75  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 6.52/2.75  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.75  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.52/2.75  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.52/2.75  tff(c_615, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.52/2.75  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.52/2.75  tff(c_437, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.52/2.75  tff(c_475, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_437])).
% 6.52/2.75  tff(c_484, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_475])).
% 6.52/2.75  tff(c_625, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(B_47, k4_xboole_0(A_46, B_47)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_615, c_484])).
% 6.52/2.75  tff(c_684, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(B_47, A_46))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_625])).
% 6.52/2.75  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.52/2.75  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.75  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 6.52/2.75  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.75  tff(c_231, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.52/2.75  tff(c_239, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_231])).
% 6.52/2.75  tff(c_297, plain, (![A_37, B_38]: (k2_xboole_0(k3_xboole_0(A_37, B_38), k4_xboole_0(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.52/2.75  tff(c_309, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_239, c_297])).
% 6.52/2.75  tff(c_146, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.52/2.75  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.52/2.75  tff(c_162, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_146, c_10])).
% 6.52/2.75  tff(c_335, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_309, c_162])).
% 6.52/2.75  tff(c_9298, plain, (![C_147]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', C_147))=k4_xboole_0('#skF_3', C_147))), inference(superposition, [status(thm), theory('equality')], [c_335, c_615])).
% 6.52/2.75  tff(c_9423, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33, c_9298])).
% 6.52/2.75  tff(c_9455, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_684, c_9423])).
% 6.52/2.75  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.75  tff(c_238, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_231])).
% 6.52/2.75  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.52/2.75  tff(c_1434, plain, (![A_66, B_67]: (k2_xboole_0(k3_xboole_0(A_66, B_67), k4_xboole_0(B_67, A_66))=B_67)), inference(superposition, [status(thm), theory('equality')], [c_4, c_297])).
% 6.52/2.75  tff(c_1520, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_238, c_1434])).
% 6.52/2.75  tff(c_1574, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1520, c_162])).
% 6.52/2.75  tff(c_696, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, A_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_625])).
% 6.52/2.75  tff(c_747, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33, c_696])).
% 6.52/2.75  tff(c_9534, plain, (![C_148, A_149, B_150]: (k2_xboole_0(C_148, k4_xboole_0(A_149, k2_xboole_0(B_150, C_148)))=k2_xboole_0(C_148, k4_xboole_0(A_149, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_615, c_14])).
% 6.52/2.75  tff(c_9783, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_747, c_9534])).
% 6.52/2.75  tff(c_9889, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_10, c_9783])).
% 6.52/2.75  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.52/2.75  tff(c_708, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k2_xboole_0(B_50, A_49))=k4_xboole_0(A_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_696, c_22])).
% 6.52/2.75  tff(c_753, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k2_xboole_0(B_50, A_49))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_708])).
% 6.52/2.75  tff(c_1001, plain, (![A_57, C_58, B_59]: (k2_xboole_0(k4_xboole_0(A_57, C_58), k4_xboole_0(B_59, C_58))=k4_xboole_0(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.52/2.75  tff(c_1072, plain, (![A_57, A_11]: (k4_xboole_0(k2_xboole_0(A_57, A_11), A_11)=k2_xboole_0(k4_xboole_0(A_57, A_11), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_484, c_1001])).
% 6.52/2.75  tff(c_2025, plain, (![A_76, A_77]: (k4_xboole_0(k2_xboole_0(A_76, A_77), A_77)=k4_xboole_0(A_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1072])).
% 6.52/2.75  tff(c_2053, plain, (![A_76, A_77]: (k4_xboole_0(k2_xboole_0(A_76, A_77), k4_xboole_0(A_76, A_77))=k3_xboole_0(k2_xboole_0(A_76, A_77), A_77))), inference(superposition, [status(thm), theory('equality')], [c_2025, c_22])).
% 6.52/2.75  tff(c_2120, plain, (![A_76, A_77]: (k4_xboole_0(k2_xboole_0(A_76, A_77), k4_xboole_0(A_76, A_77))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_753, c_4, c_2053])).
% 6.52/2.75  tff(c_9935, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_9889, c_2120])).
% 6.52/2.75  tff(c_9979, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_9455, c_9935])).
% 6.52/2.75  tff(c_9981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_9979])).
% 6.52/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.75  
% 6.52/2.75  Inference rules
% 6.52/2.75  ----------------------
% 6.52/2.75  #Ref     : 0
% 6.52/2.75  #Sup     : 2545
% 6.52/2.75  #Fact    : 0
% 6.52/2.75  #Define  : 0
% 6.52/2.75  #Split   : 0
% 6.52/2.75  #Chain   : 0
% 6.52/2.75  #Close   : 0
% 6.52/2.75  
% 6.52/2.75  Ordering : KBO
% 6.52/2.75  
% 6.52/2.75  Simplification rules
% 6.52/2.75  ----------------------
% 6.52/2.75  #Subsume      : 17
% 6.52/2.75  #Demod        : 2832
% 6.52/2.75  #Tautology    : 1614
% 6.52/2.75  #SimpNegUnit  : 1
% 6.52/2.75  #BackRed      : 7
% 6.52/2.75  
% 6.52/2.75  #Partial instantiations: 0
% 6.52/2.75  #Strategies tried      : 1
% 6.52/2.75  
% 6.52/2.75  Timing (in seconds)
% 6.52/2.75  ----------------------
% 6.52/2.75  Preprocessing        : 0.35
% 6.52/2.75  Parsing              : 0.23
% 6.52/2.75  CNF conversion       : 0.02
% 6.52/2.75  Main loop            : 1.50
% 6.52/2.75  Inferencing          : 0.37
% 6.52/2.75  Reduction            : 0.81
% 6.52/2.75  Demodulation         : 0.70
% 6.52/2.75  BG Simplification    : 0.05
% 6.52/2.75  Subsumption          : 0.20
% 6.52/2.75  Abstraction          : 0.07
% 6.52/2.75  MUC search           : 0.00
% 6.52/2.75  Cooper               : 0.00
% 6.52/2.75  Total                : 1.89
% 6.52/2.75  Index Insertion      : 0.00
% 6.52/2.75  Index Deletion       : 0.00
% 6.52/2.75  Index Matching       : 0.00
% 6.52/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
