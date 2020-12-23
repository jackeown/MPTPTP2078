%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 125 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :   57 ( 137 expanded)
%              Number of equality atoms :   43 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_201,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_209,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_32])).

tff(c_257,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_266,plain,(
    ! [A_44,B_45] : k4_xboole_0(k3_xboole_0(A_44,B_45),A_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_74])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_301,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_257])).

tff(c_314,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_210,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_210])).

tff(c_243,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_233])).

tff(c_523,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k4_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_607,plain,(
    ! [C_58,B_59] : k3_xboole_0(C_58,k4_xboole_0(B_59,C_58)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_266])).

tff(c_641,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_607])).

tff(c_1673,plain,(
    ! [A_81,B_82,C_83] : k3_xboole_0(k3_xboole_0(A_81,B_82),C_83) = k3_xboole_0(A_81,k3_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1768,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_1673])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1951,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_22])).

tff(c_1959,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1951])).

tff(c_530,plain,(
    ! [C_57,B_56] : k3_xboole_0(C_57,k4_xboole_0(B_56,C_57)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_266])).

tff(c_2035,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_530])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k3_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k3_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2063,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2035,c_10])).

tff(c_2109,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2063,c_22])).

tff(c_2117,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2109])).

tff(c_5243,plain,(
    ! [C_123] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_123)) = k4_xboole_0('#skF_1',C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_523])).

tff(c_5295,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_5243])).

tff(c_5342,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_5295])).

tff(c_624,plain,(
    ! [C_58,B_59] : k4_xboole_0(C_58,k4_xboole_0(B_59,C_58)) = k4_xboole_0(C_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_22])).

tff(c_665,plain,(
    ! [C_58,B_59] : k4_xboole_0(C_58,k4_xboole_0(B_59,C_58)) = C_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_624])).

tff(c_6288,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5342,c_665])).

tff(c_6319,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_6288])).

tff(c_6321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_6319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.95  
% 4.86/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.95  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.86/1.95  
% 4.86/1.95  %Foreground sorts:
% 4.86/1.95  
% 4.86/1.95  
% 4.86/1.95  %Background operators:
% 4.86/1.95  
% 4.86/1.95  
% 4.86/1.95  %Foreground operators:
% 4.86/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.86/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.95  
% 4.86/1.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.86/1.96  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.86/1.96  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.86/1.96  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.86/1.96  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.86/1.96  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.86/1.96  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.86/1.96  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.86/1.96  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.86/1.96  tff(c_201, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/1.96  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.86/1.96  tff(c_209, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_32])).
% 4.86/1.96  tff(c_257, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.86/1.96  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.86/1.96  tff(c_63, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.86/1.96  tff(c_74, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_63])).
% 4.86/1.96  tff(c_266, plain, (![A_44, B_45]: (k4_xboole_0(k3_xboole_0(A_44, B_45), A_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_74])).
% 4.86/1.96  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.96  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.86/1.96  tff(c_75, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_63])).
% 4.86/1.96  tff(c_301, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_75, c_257])).
% 4.86/1.96  tff(c_314, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_301])).
% 4.86/1.96  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.86/1.96  tff(c_54, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/1.96  tff(c_58, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_54])).
% 4.86/1.96  tff(c_210, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.86/1.96  tff(c_233, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_210])).
% 4.86/1.96  tff(c_243, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_233])).
% 4.86/1.96  tff(c_523, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k4_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.86/1.96  tff(c_607, plain, (![C_58, B_59]: (k3_xboole_0(C_58, k4_xboole_0(B_59, C_58))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_523, c_266])).
% 4.86/1.96  tff(c_641, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_243, c_607])).
% 4.86/1.96  tff(c_1673, plain, (![A_81, B_82, C_83]: (k3_xboole_0(k3_xboole_0(A_81, B_82), C_83)=k3_xboole_0(A_81, k3_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.96  tff(c_1768, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_641, c_1673])).
% 4.86/1.96  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.86/1.96  tff(c_1951, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1768, c_22])).
% 4.86/1.96  tff(c_1959, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1951])).
% 4.86/1.96  tff(c_530, plain, (![C_57, B_56]: (k3_xboole_0(C_57, k4_xboole_0(B_56, C_57))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_523, c_266])).
% 4.86/1.96  tff(c_2035, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1959, c_530])).
% 4.86/1.96  tff(c_10, plain, (![A_5, B_6, C_7]: (k3_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.96  tff(c_2063, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2035, c_10])).
% 4.86/1.96  tff(c_2109, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2063, c_22])).
% 4.86/1.96  tff(c_2117, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2109])).
% 4.86/1.96  tff(c_5243, plain, (![C_123]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_123))=k4_xboole_0('#skF_1', C_123))), inference(superposition, [status(thm), theory('equality')], [c_314, c_523])).
% 4.86/1.96  tff(c_5295, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2117, c_5243])).
% 4.86/1.96  tff(c_5342, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_5295])).
% 4.86/1.96  tff(c_624, plain, (![C_58, B_59]: (k4_xboole_0(C_58, k4_xboole_0(B_59, C_58))=k4_xboole_0(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_607, c_22])).
% 4.86/1.96  tff(c_665, plain, (![C_58, B_59]: (k4_xboole_0(C_58, k4_xboole_0(B_59, C_58))=C_58)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_624])).
% 4.86/1.96  tff(c_6288, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5342, c_665])).
% 4.86/1.96  tff(c_6319, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_266, c_6288])).
% 4.86/1.96  tff(c_6321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_6319])).
% 4.86/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.96  
% 4.86/1.96  Inference rules
% 4.86/1.96  ----------------------
% 4.86/1.96  #Ref     : 0
% 4.86/1.96  #Sup     : 1569
% 4.86/1.96  #Fact    : 0
% 4.86/1.96  #Define  : 0
% 4.86/1.96  #Split   : 0
% 4.86/1.96  #Chain   : 0
% 4.86/1.96  #Close   : 0
% 4.86/1.96  
% 4.86/1.96  Ordering : KBO
% 4.86/1.96  
% 4.86/1.96  Simplification rules
% 4.86/1.96  ----------------------
% 4.86/1.96  #Subsume      : 13
% 4.86/1.96  #Demod        : 1449
% 4.86/1.96  #Tautology    : 1095
% 4.86/1.96  #SimpNegUnit  : 1
% 4.86/1.96  #BackRed      : 0
% 4.86/1.96  
% 4.86/1.96  #Partial instantiations: 0
% 4.86/1.96  #Strategies tried      : 1
% 4.86/1.96  
% 4.86/1.96  Timing (in seconds)
% 4.86/1.96  ----------------------
% 4.86/1.97  Preprocessing        : 0.29
% 4.86/1.97  Parsing              : 0.16
% 4.86/1.97  CNF conversion       : 0.02
% 4.86/1.97  Main loop            : 0.90
% 4.86/1.97  Inferencing          : 0.29
% 4.86/1.97  Reduction            : 0.40
% 4.86/1.97  Demodulation         : 0.33
% 4.86/1.97  BG Simplification    : 0.03
% 4.86/1.97  Subsumption          : 0.13
% 4.86/1.97  Abstraction          : 0.05
% 4.86/1.97  MUC search           : 0.00
% 4.86/1.97  Cooper               : 0.00
% 4.86/1.97  Total                : 1.22
% 4.86/1.97  Index Insertion      : 0.00
% 4.86/1.97  Index Deletion       : 0.00
% 4.86/1.97  Index Matching       : 0.00
% 4.86/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
