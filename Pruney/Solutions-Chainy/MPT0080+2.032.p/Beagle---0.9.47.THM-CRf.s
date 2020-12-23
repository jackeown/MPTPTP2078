%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:53 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 114 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 122 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_171,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_22])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_21,B_20] : r1_tarski(A_21,k2_xboole_0(B_20,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_20])).

tff(c_176,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_21,B_20] : k4_xboole_0(A_21,k2_xboole_0(B_20,A_21)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_489,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2383,plain,(
    ! [C_90,A_91,B_92] : k2_xboole_0(C_90,k4_xboole_0(A_91,k2_xboole_0(B_92,C_90))) = k2_xboole_0(C_90,k4_xboole_0(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_14])).

tff(c_2509,plain,(
    ! [A_21,B_20] : k2_xboole_0(A_21,k4_xboole_0(A_21,B_20)) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2383])).

tff(c_2571,plain,(
    ! [A_21,B_20] : k2_xboole_0(A_21,k4_xboole_0(A_21,B_20)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2509])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_418,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_390])).

tff(c_444,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_418])).

tff(c_3078,plain,(
    ! [A_99,B_100] : k2_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2571,c_444])).

tff(c_3219,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_3078])).

tff(c_199,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_176])).

tff(c_424,plain,(
    ! [A_15,B_16] : k2_xboole_0(k2_xboole_0(A_15,B_16),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_390])).

tff(c_890,plain,(
    ! [A_60,B_61] : k2_xboole_0(k2_xboole_0(A_60,B_61),A_60) = k2_xboole_0(A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_424])).

tff(c_949,plain,(
    ! [B_2,B_61] : k2_xboole_0(B_2,k2_xboole_0(B_2,B_61)) = k2_xboole_0(B_2,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_890])).

tff(c_3260,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3219,c_949])).

tff(c_3328,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2571,c_2,c_12,c_3260])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_200,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27,c_176])).

tff(c_2515,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2383])).

tff(c_2573,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2515])).

tff(c_2621,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2573,c_196])).

tff(c_3345,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_2621])).

tff(c_3351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_3345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.65  
% 3.68/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.65  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.68/1.65  
% 3.68/1.65  %Foreground sorts:
% 3.68/1.65  
% 3.68/1.65  
% 3.68/1.65  %Background operators:
% 3.68/1.65  
% 3.68/1.65  
% 3.68/1.65  %Foreground operators:
% 3.68/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.65  
% 3.68/1.66  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.68/1.66  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.68/1.66  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.68/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.68/1.66  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.68/1.66  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.68/1.66  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.68/1.66  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.68/1.66  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.68/1.66  tff(c_171, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.66  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.66  tff(c_175, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_171, c_22])).
% 3.68/1.66  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.66  tff(c_41, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.66  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.68/1.66  tff(c_56, plain, (![A_21, B_20]: (r1_tarski(A_21, k2_xboole_0(B_20, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_20])).
% 3.68/1.66  tff(c_176, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.66  tff(c_196, plain, (![A_21, B_20]: (k4_xboole_0(A_21, k2_xboole_0(B_20, A_21))=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_176])).
% 3.68/1.66  tff(c_489, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.68/1.66  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.66  tff(c_2383, plain, (![C_90, A_91, B_92]: (k2_xboole_0(C_90, k4_xboole_0(A_91, k2_xboole_0(B_92, C_90)))=k2_xboole_0(C_90, k4_xboole_0(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_489, c_14])).
% 3.68/1.66  tff(c_2509, plain, (![A_21, B_20]: (k2_xboole_0(A_21, k4_xboole_0(A_21, B_20))=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2383])).
% 3.68/1.66  tff(c_2571, plain, (![A_21, B_20]: (k2_xboole_0(A_21, k4_xboole_0(A_21, B_20))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2509])).
% 3.68/1.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.66  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.66  tff(c_136, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.66  tff(c_140, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_136])).
% 3.68/1.66  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.66  tff(c_390, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.66  tff(c_418, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(k4_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_390])).
% 3.68/1.66  tff(c_444, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_418])).
% 3.68/1.66  tff(c_3078, plain, (![A_99, B_100]: (k2_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_2571, c_444])).
% 3.68/1.66  tff(c_3219, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_140, c_3078])).
% 3.68/1.66  tff(c_199, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_176])).
% 3.68/1.66  tff(c_424, plain, (![A_15, B_16]: (k2_xboole_0(k2_xboole_0(A_15, B_16), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_199, c_390])).
% 3.68/1.66  tff(c_890, plain, (![A_60, B_61]: (k2_xboole_0(k2_xboole_0(A_60, B_61), A_60)=k2_xboole_0(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_424])).
% 3.68/1.66  tff(c_949, plain, (![B_2, B_61]: (k2_xboole_0(B_2, k2_xboole_0(B_2, B_61))=k2_xboole_0(B_2, B_61))), inference(superposition, [status(thm), theory('equality')], [c_2, c_890])).
% 3.68/1.66  tff(c_3260, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3219, c_949])).
% 3.68/1.66  tff(c_3328, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2571, c_2, c_12, c_3260])).
% 3.68/1.66  tff(c_26, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.66  tff(c_27, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 3.68/1.66  tff(c_200, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27, c_176])).
% 3.68/1.66  tff(c_2515, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_200, c_2383])).
% 3.68/1.66  tff(c_2573, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2515])).
% 3.68/1.66  tff(c_2621, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2573, c_196])).
% 3.68/1.66  tff(c_3345, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3328, c_2621])).
% 3.68/1.66  tff(c_3351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_3345])).
% 3.68/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.66  
% 3.68/1.66  Inference rules
% 3.68/1.66  ----------------------
% 3.68/1.66  #Ref     : 0
% 3.68/1.66  #Sup     : 832
% 3.68/1.66  #Fact    : 0
% 3.68/1.66  #Define  : 0
% 3.68/1.66  #Split   : 0
% 3.68/1.66  #Chain   : 0
% 3.68/1.66  #Close   : 0
% 3.68/1.66  
% 3.68/1.66  Ordering : KBO
% 3.68/1.66  
% 3.68/1.66  Simplification rules
% 3.68/1.66  ----------------------
% 3.68/1.66  #Subsume      : 2
% 3.68/1.66  #Demod        : 795
% 3.68/1.66  #Tautology    : 586
% 3.68/1.66  #SimpNegUnit  : 1
% 3.68/1.66  #BackRed      : 7
% 3.68/1.66  
% 3.68/1.66  #Partial instantiations: 0
% 3.68/1.66  #Strategies tried      : 1
% 3.68/1.66  
% 3.68/1.66  Timing (in seconds)
% 3.68/1.66  ----------------------
% 4.02/1.66  Preprocessing        : 0.26
% 4.02/1.66  Parsing              : 0.15
% 4.02/1.66  CNF conversion       : 0.02
% 4.02/1.66  Main loop            : 0.64
% 4.02/1.66  Inferencing          : 0.19
% 4.02/1.67  Reduction            : 0.30
% 4.02/1.67  Demodulation         : 0.25
% 4.02/1.67  BG Simplification    : 0.02
% 4.02/1.67  Subsumption          : 0.09
% 4.02/1.67  Abstraction          : 0.03
% 4.02/1.67  MUC search           : 0.00
% 4.02/1.67  Cooper               : 0.00
% 4.02/1.67  Total                : 0.93
% 4.02/1.67  Index Insertion      : 0.00
% 4.02/1.67  Index Deletion       : 0.00
% 4.02/1.67  Index Matching       : 0.00
% 4.02/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
