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
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   45 (  82 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_93,plain,(
    ! [A_35,B_36] : k2_xboole_0(k3_xboole_0(A_35,B_36),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_58,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_45,c_48])).

tff(c_207,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k5_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_9] : k4_xboole_0(A_9,k3_xboole_0(A_9,A_9)) = k5_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_207])).

tff(c_281,plain,(
    ! [A_51] : k4_xboole_0(A_51,k3_xboole_0(A_51,A_51)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_299,plain,(
    ! [A_51] : k2_xboole_0(k3_xboole_0(A_51,A_51),k1_xboole_0) = k2_xboole_0(k3_xboole_0(A_51,A_51),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_14])).

tff(c_320,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12,c_299])).

tff(c_237,plain,(
    ! [A_9] : k4_xboole_0(A_9,k3_xboole_0(A_9,A_9)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_370,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_237])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k3_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(A_15,C_17)) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_375,plain,(
    ! [A_53,C_17] : k4_xboole_0(A_53,k2_xboole_0(A_53,C_17)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_53,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_18])).

tff(c_405,plain,(
    ! [A_54,C_55] : k4_xboole_0(A_54,k2_xboole_0(A_54,C_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_375])).

tff(c_505,plain,(
    ! [A_57,B_58] : k4_xboole_0(k3_xboole_0(A_57,B_58),A_57) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_405])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_542,plain,(
    ! [A_59,B_60] : k3_xboole_0(A_59,k4_xboole_0(B_60,A_59)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_16])).

tff(c_587,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),k5_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_542])).

tff(c_84,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_92,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_24])).

tff(c_2410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.13/1.47  
% 3.13/1.47  %Foreground sorts:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Background operators:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Foreground operators:
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.47  
% 3.13/1.48  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 3.13/1.48  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.13/1.48  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.13/1.48  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.13/1.48  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.13/1.48  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.13/1.48  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.13/1.48  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 3.13/1.48  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.13/1.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.13/1.48  tff(f_52, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 3.13/1.48  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.48  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.48  tff(c_48, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.48  tff(c_60, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_10, c_48])).
% 3.13/1.48  tff(c_93, plain, (![A_35, B_36]: (k2_xboole_0(k3_xboole_0(A_35, B_36), A_35)=A_35)), inference(resolution, [status(thm)], [c_10, c_48])).
% 3.13/1.48  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.48  tff(c_103, plain, (![B_36]: (k3_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 3.13/1.48  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.48  tff(c_42, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.13/1.48  tff(c_45, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_42])).
% 3.13/1.48  tff(c_58, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(resolution, [status(thm)], [c_45, c_48])).
% 3.13/1.48  tff(c_207, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k5_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.48  tff(c_231, plain, (![A_9]: (k4_xboole_0(A_9, k3_xboole_0(A_9, A_9))=k5_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_58, c_207])).
% 3.13/1.48  tff(c_281, plain, (![A_51]: (k4_xboole_0(A_51, k3_xboole_0(A_51, A_51))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_231])).
% 3.13/1.48  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.48  tff(c_299, plain, (![A_51]: (k2_xboole_0(k3_xboole_0(A_51, A_51), k1_xboole_0)=k2_xboole_0(k3_xboole_0(A_51, A_51), A_51))), inference(superposition, [status(thm), theory('equality')], [c_281, c_14])).
% 3.13/1.48  tff(c_320, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12, c_299])).
% 3.13/1.48  tff(c_237, plain, (![A_9]: (k4_xboole_0(A_9, k3_xboole_0(A_9, A_9))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_231])).
% 3.13/1.48  tff(c_370, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_320, c_237])).
% 3.13/1.48  tff(c_18, plain, (![A_15, B_16, C_17]: (k3_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(A_15, C_17))=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.48  tff(c_375, plain, (![A_53, C_17]: (k4_xboole_0(A_53, k2_xboole_0(A_53, C_17))=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_53, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_370, c_18])).
% 3.13/1.48  tff(c_405, plain, (![A_54, C_55]: (k4_xboole_0(A_54, k2_xboole_0(A_54, C_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_375])).
% 3.13/1.48  tff(c_505, plain, (![A_57, B_58]: (k4_xboole_0(k3_xboole_0(A_57, B_58), A_57)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_405])).
% 3.13/1.48  tff(c_16, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_542, plain, (![A_59, B_60]: (k3_xboole_0(A_59, k4_xboole_0(B_60, A_59))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_505, c_16])).
% 3.13/1.48  tff(c_587, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), k5_xboole_0(A_3, B_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_542])).
% 3.13/1.48  tff(c_84, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.48  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.48  tff(c_92, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_24])).
% 3.13/1.48  tff(c_2410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_587, c_92])).
% 3.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  Inference rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Ref     : 0
% 3.13/1.48  #Sup     : 584
% 3.13/1.48  #Fact    : 0
% 3.13/1.48  #Define  : 0
% 3.13/1.48  #Split   : 0
% 3.13/1.48  #Chain   : 0
% 3.13/1.48  #Close   : 0
% 3.13/1.48  
% 3.13/1.48  Ordering : KBO
% 3.13/1.48  
% 3.13/1.48  Simplification rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Subsume      : 0
% 3.13/1.48  #Demod        : 532
% 3.13/1.48  #Tautology    : 423
% 3.13/1.48  #SimpNegUnit  : 0
% 3.13/1.48  #BackRed      : 3
% 3.13/1.48  
% 3.13/1.48  #Partial instantiations: 0
% 3.13/1.48  #Strategies tried      : 1
% 3.13/1.48  
% 3.13/1.48  Timing (in seconds)
% 3.13/1.49  ----------------------
% 3.13/1.49  Preprocessing        : 0.27
% 3.13/1.49  Parsing              : 0.15
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.46
% 3.29/1.49  Inferencing          : 0.17
% 3.29/1.49  Reduction            : 0.18
% 3.29/1.49  Demodulation         : 0.14
% 3.29/1.49  BG Simplification    : 0.02
% 3.29/1.49  Subsumption          : 0.05
% 3.29/1.49  Abstraction          : 0.03
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.76
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
