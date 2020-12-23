%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 130 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_149,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_162,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_184,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_180])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [A_32,B_33,C_34] : k4_xboole_0(k3_xboole_0(A_32,B_33),C_34) = k3_xboole_0(A_32,k4_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_253,plain,(
    ! [A_32,B_33,B_9] : k3_xboole_0(A_32,k4_xboole_0(B_33,k4_xboole_0(k3_xboole_0(A_32,B_33),B_9))) = k3_xboole_0(k3_xboole_0(A_32,B_33),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_14])).

tff(c_2591,plain,(
    ! [A_75,B_76,B_77] : k3_xboole_0(A_75,k4_xboole_0(B_76,k3_xboole_0(A_75,k4_xboole_0(B_76,B_77)))) = k3_xboole_0(k3_xboole_0(A_75,B_76),B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_2755,plain,(
    ! [A_75,A_7] : k3_xboole_0(k3_xboole_0(A_75,A_7),A_7) = k3_xboole_0(A_75,k4_xboole_0(A_7,k3_xboole_0(A_75,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2591])).

tff(c_2826,plain,(
    ! [A_78,A_79] : k3_xboole_0(k3_xboole_0(A_78,A_79),A_79) = k3_xboole_0(A_78,A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77,c_2755])).

tff(c_3287,plain,(
    ! [A_83,B_84] : k3_xboole_0(k3_xboole_0(A_83,B_84),A_83) = k3_xboole_0(B_84,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2826])).

tff(c_3438,plain,(
    ! [A_1,B_84] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_84)) = k3_xboole_0(B_84,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3287])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_140])).

tff(c_2761,plain,(
    ! [A_75] : k3_xboole_0(A_75,k4_xboole_0('#skF_1',k3_xboole_0(A_75,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(A_75,'#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2591])).

tff(c_2822,plain,(
    ! [A_75] : k3_xboole_0('#skF_3',k3_xboole_0(A_75,'#skF_1')) = k3_xboole_0(A_75,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77,c_2,c_2761])).

tff(c_78,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_83,plain,(
    ! [A_20] : k3_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_280,plain,(
    ! [A_20,C_34] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_20,C_34)) = k4_xboole_0(k1_xboole_0,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_239])).

tff(c_300,plain,(
    ! [C_34] : k4_xboole_0(k1_xboole_0,C_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_280])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_76,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_69])).

tff(c_277,plain,(
    ! [C_34] : k3_xboole_0('#skF_1',k4_xboole_0(k3_xboole_0('#skF_3','#skF_2'),C_34)) = k4_xboole_0(k1_xboole_0,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_239])).

tff(c_299,plain,(
    ! [C_34] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_34))) = k4_xboole_0(k1_xboole_0,C_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_1617,plain,(
    ! [C_62] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_62))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_299])).

tff(c_4517,plain,(
    ! [B_95] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_95))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1617])).

tff(c_4578,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2822,c_4517])).

tff(c_4622,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3438,c_2,c_4578])).

tff(c_4624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_4622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.82  
% 4.52/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.82  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.58/1.82  
% 4.58/1.82  %Foreground sorts:
% 4.58/1.82  
% 4.58/1.82  
% 4.58/1.82  %Background operators:
% 4.58/1.82  
% 4.58/1.82  
% 4.58/1.82  %Foreground operators:
% 4.58/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.58/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.58/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.58/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.58/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.58/1.82  
% 4.58/1.84  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.58/1.84  tff(f_52, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.58/1.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.58/1.84  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.58/1.84  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.58/1.84  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.58/1.84  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.58/1.84  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.58/1.84  tff(c_149, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.84  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.84  tff(c_157, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_24])).
% 4.58/1.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.58/1.84  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.84  tff(c_18, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.84  tff(c_69, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.84  tff(c_77, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_69])).
% 4.58/1.84  tff(c_162, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.84  tff(c_180, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_162])).
% 4.58/1.84  tff(c_184, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_180])).
% 4.58/1.84  tff(c_16, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.84  tff(c_239, plain, (![A_32, B_33, C_34]: (k4_xboole_0(k3_xboole_0(A_32, B_33), C_34)=k3_xboole_0(A_32, k4_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.84  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.84  tff(c_253, plain, (![A_32, B_33, B_9]: (k3_xboole_0(A_32, k4_xboole_0(B_33, k4_xboole_0(k3_xboole_0(A_32, B_33), B_9)))=k3_xboole_0(k3_xboole_0(A_32, B_33), B_9))), inference(superposition, [status(thm), theory('equality')], [c_239, c_14])).
% 4.58/1.84  tff(c_2591, plain, (![A_75, B_76, B_77]: (k3_xboole_0(A_75, k4_xboole_0(B_76, k3_xboole_0(A_75, k4_xboole_0(B_76, B_77))))=k3_xboole_0(k3_xboole_0(A_75, B_76), B_77))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_253])).
% 4.58/1.84  tff(c_2755, plain, (![A_75, A_7]: (k3_xboole_0(k3_xboole_0(A_75, A_7), A_7)=k3_xboole_0(A_75, k4_xboole_0(A_7, k3_xboole_0(A_75, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_2591])).
% 4.58/1.84  tff(c_2826, plain, (![A_78, A_79]: (k3_xboole_0(k3_xboole_0(A_78, A_79), A_79)=k3_xboole_0(A_78, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77, c_2755])).
% 4.58/1.84  tff(c_3287, plain, (![A_83, B_84]: (k3_xboole_0(k3_xboole_0(A_83, B_84), A_83)=k3_xboole_0(B_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2826])).
% 4.58/1.84  tff(c_3438, plain, (![A_1, B_84]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_84))=k3_xboole_0(B_84, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3287])).
% 4.58/1.84  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.84  tff(c_140, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.58/1.84  tff(c_148, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_140])).
% 4.58/1.84  tff(c_2761, plain, (![A_75]: (k3_xboole_0(A_75, k4_xboole_0('#skF_1', k3_xboole_0(A_75, k1_xboole_0)))=k3_xboole_0(k3_xboole_0(A_75, '#skF_1'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_2591])).
% 4.58/1.84  tff(c_2822, plain, (![A_75]: (k3_xboole_0('#skF_3', k3_xboole_0(A_75, '#skF_1'))=k3_xboole_0(A_75, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77, c_2, c_2761])).
% 4.58/1.84  tff(c_78, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_69])).
% 4.58/1.84  tff(c_83, plain, (![A_20]: (k3_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 4.58/1.84  tff(c_280, plain, (![A_20, C_34]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_20, C_34))=k4_xboole_0(k1_xboole_0, C_34))), inference(superposition, [status(thm), theory('equality')], [c_83, c_239])).
% 4.58/1.84  tff(c_300, plain, (![C_34]: (k4_xboole_0(k1_xboole_0, C_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_280])).
% 4.58/1.84  tff(c_20, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.58/1.84  tff(c_25, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 4.58/1.84  tff(c_76, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_69])).
% 4.58/1.84  tff(c_277, plain, (![C_34]: (k3_xboole_0('#skF_1', k4_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), C_34))=k4_xboole_0(k1_xboole_0, C_34))), inference(superposition, [status(thm), theory('equality')], [c_76, c_239])).
% 4.58/1.84  tff(c_299, plain, (![C_34]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_34)))=k4_xboole_0(k1_xboole_0, C_34))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_277])).
% 4.58/1.84  tff(c_1617, plain, (![C_62]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_62)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_299])).
% 4.58/1.84  tff(c_4517, plain, (![B_95]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_95)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1617])).
% 4.58/1.84  tff(c_4578, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2822, c_4517])).
% 4.58/1.84  tff(c_4622, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3438, c_2, c_4578])).
% 4.58/1.84  tff(c_4624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_4622])).
% 4.58/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.84  
% 4.58/1.84  Inference rules
% 4.58/1.84  ----------------------
% 4.58/1.84  #Ref     : 0
% 4.58/1.84  #Sup     : 1138
% 4.58/1.84  #Fact    : 0
% 4.58/1.84  #Define  : 0
% 4.58/1.84  #Split   : 0
% 4.58/1.84  #Chain   : 0
% 4.58/1.84  #Close   : 0
% 4.58/1.84  
% 4.58/1.84  Ordering : KBO
% 4.58/1.84  
% 4.58/1.84  Simplification rules
% 4.58/1.84  ----------------------
% 4.58/1.84  #Subsume      : 4
% 4.58/1.84  #Demod        : 1413
% 4.58/1.84  #Tautology    : 777
% 4.58/1.84  #SimpNegUnit  : 1
% 4.58/1.84  #BackRed      : 5
% 4.58/1.84  
% 4.58/1.84  #Partial instantiations: 0
% 4.58/1.84  #Strategies tried      : 1
% 4.58/1.84  
% 4.58/1.84  Timing (in seconds)
% 4.58/1.84  ----------------------
% 4.58/1.84  Preprocessing        : 0.27
% 4.58/1.84  Parsing              : 0.14
% 4.58/1.84  CNF conversion       : 0.02
% 4.58/1.84  Main loop            : 0.82
% 4.58/1.84  Inferencing          : 0.23
% 4.58/1.84  Reduction            : 0.42
% 4.58/1.84  Demodulation         : 0.36
% 4.58/1.84  BG Simplification    : 0.03
% 4.58/1.84  Subsumption          : 0.10
% 4.58/1.84  Abstraction          : 0.04
% 4.58/1.84  MUC search           : 0.00
% 4.58/1.84  Cooper               : 0.00
% 4.58/1.84  Total                : 1.11
% 4.58/1.84  Index Insertion      : 0.00
% 4.58/1.84  Index Deletion       : 0.00
% 4.58/1.84  Index Matching       : 0.00
% 4.58/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
