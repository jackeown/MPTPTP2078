%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 16.55s
% Output     : CNFRefutation 16.55s
% Verified   : 
% Statistics : Number of formulae       :   37 (  75 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  66 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_8])).

tff(c_314,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k4_xboole_0(A_3,B_4),C_5) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_254,plain,(
    ! [A_28,B_29,C_30] : k4_xboole_0(k3_xboole_0(A_28,B_29),C_30) = k3_xboole_0(A_28,k4_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_365,plain,(
    ! [B_33,A_34,C_35] : k4_xboole_0(k3_xboole_0(B_33,A_34),C_35) = k3_xboole_0(A_34,k4_xboole_0(B_33,C_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_254])).

tff(c_398,plain,(
    ! [A_15,B_16,C_35] : k3_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(A_15,C_35)) = k4_xboole_0(k4_xboole_0(A_15,B_16),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_365])).

tff(c_31044,plain,(
    ! [A_209,B_210,C_211] : k3_xboole_0(k4_xboole_0(A_209,B_210),k4_xboole_0(A_209,C_211)) = k4_xboole_0(A_209,k2_xboole_0(B_210,C_211)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_398])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_444,plain,(
    ! [B_36,A_37,C_38] : k3_xboole_0(B_36,k4_xboole_0(A_37,C_38)) = k3_xboole_0(A_37,k4_xboole_0(B_36,C_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_365])).

tff(c_556,plain,(
    ! [A_37,C_38,A_1] : k3_xboole_0(k4_xboole_0(A_37,C_38),A_1) = k3_xboole_0(A_37,k4_xboole_0(A_1,C_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_444])).

tff(c_31262,plain,(
    ! [A_209,C_211,B_210] : k3_xboole_0(A_209,k4_xboole_0(k4_xboole_0(A_209,C_211),B_210)) = k4_xboole_0(A_209,k2_xboole_0(B_210,C_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_31044,c_556])).

tff(c_31587,plain,(
    ! [A_209,C_211,B_210] : k4_xboole_0(A_209,k2_xboole_0(C_211,B_210)) = k4_xboole_0(A_209,k2_xboole_0(B_210,C_211)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_4,c_31262])).

tff(c_401,plain,(
    ! [B_11,A_10,C_12] : k3_xboole_0(B_11,k4_xboole_0(A_10,C_12)) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_365])).

tff(c_12,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_442,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_13])).

tff(c_443,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_4,c_442])).

tff(c_31666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31587,c_443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.55/8.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.55/8.07  
% 16.55/8.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.55/8.07  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 16.55/8.07  
% 16.55/8.07  %Foreground sorts:
% 16.55/8.07  
% 16.55/8.07  
% 16.55/8.07  %Background operators:
% 16.55/8.07  
% 16.55/8.07  
% 16.55/8.07  %Foreground operators:
% 16.55/8.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.55/8.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.55/8.07  tff('#skF_2', type, '#skF_2': $i).
% 16.55/8.07  tff('#skF_3', type, '#skF_3': $i).
% 16.55/8.07  tff('#skF_1', type, '#skF_1': $i).
% 16.55/8.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.55/8.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.55/8.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.55/8.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.55/8.07  
% 16.55/8.08  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.55/8.08  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.55/8.08  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 16.55/8.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.55/8.08  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 16.55/8.08  tff(f_38, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 16.55/8.08  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.55/8.08  tff(c_47, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.55/8.08  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.55/8.08  tff(c_50, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_8])).
% 16.55/8.08  tff(c_314, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 16.55/8.08  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_xboole_0(k4_xboole_0(A_3, B_4), C_5)=k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.55/8.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.55/8.08  tff(c_254, plain, (![A_28, B_29, C_30]: (k4_xboole_0(k3_xboole_0(A_28, B_29), C_30)=k3_xboole_0(A_28, k4_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.55/8.08  tff(c_365, plain, (![B_33, A_34, C_35]: (k4_xboole_0(k3_xboole_0(B_33, A_34), C_35)=k3_xboole_0(A_34, k4_xboole_0(B_33, C_35)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_254])).
% 16.55/8.08  tff(c_398, plain, (![A_15, B_16, C_35]: (k3_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(A_15, C_35))=k4_xboole_0(k4_xboole_0(A_15, B_16), C_35))), inference(superposition, [status(thm), theory('equality')], [c_314, c_365])).
% 16.55/8.08  tff(c_31044, plain, (![A_209, B_210, C_211]: (k3_xboole_0(k4_xboole_0(A_209, B_210), k4_xboole_0(A_209, C_211))=k4_xboole_0(A_209, k2_xboole_0(B_210, C_211)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_398])).
% 16.55/8.08  tff(c_10, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.55/8.08  tff(c_444, plain, (![B_36, A_37, C_38]: (k3_xboole_0(B_36, k4_xboole_0(A_37, C_38))=k3_xboole_0(A_37, k4_xboole_0(B_36, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_365])).
% 16.55/8.08  tff(c_556, plain, (![A_37, C_38, A_1]: (k3_xboole_0(k4_xboole_0(A_37, C_38), A_1)=k3_xboole_0(A_37, k4_xboole_0(A_1, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_444])).
% 16.55/8.08  tff(c_31262, plain, (![A_209, C_211, B_210]: (k3_xboole_0(A_209, k4_xboole_0(k4_xboole_0(A_209, C_211), B_210))=k4_xboole_0(A_209, k2_xboole_0(B_210, C_211)))), inference(superposition, [status(thm), theory('equality')], [c_31044, c_556])).
% 16.55/8.08  tff(c_31587, plain, (![A_209, C_211, B_210]: (k4_xboole_0(A_209, k2_xboole_0(C_211, B_210))=k4_xboole_0(A_209, k2_xboole_0(B_210, C_211)))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_4, c_31262])).
% 16.55/8.08  tff(c_401, plain, (![B_11, A_10, C_12]: (k3_xboole_0(B_11, k4_xboole_0(A_10, C_12))=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_365])).
% 16.55/8.08  tff(c_12, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.55/8.08  tff(c_13, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 16.55/8.08  tff(c_442, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_13])).
% 16.55/8.08  tff(c_443, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_4, c_442])).
% 16.55/8.08  tff(c_31666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31587, c_443])).
% 16.55/8.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.55/8.08  
% 16.55/8.08  Inference rules
% 16.55/8.08  ----------------------
% 16.55/8.08  #Ref     : 0
% 16.55/8.08  #Sup     : 7740
% 16.55/8.08  #Fact    : 0
% 16.55/8.08  #Define  : 0
% 16.55/8.08  #Split   : 0
% 16.55/8.08  #Chain   : 0
% 16.55/8.08  #Close   : 0
% 16.55/8.08  
% 16.55/8.08  Ordering : KBO
% 16.55/8.08  
% 16.55/8.08  Simplification rules
% 16.55/8.08  ----------------------
% 16.55/8.08  #Subsume      : 1001
% 16.55/8.08  #Demod        : 13003
% 16.55/8.08  #Tautology    : 2142
% 16.55/8.08  #SimpNegUnit  : 0
% 16.55/8.08  #BackRed      : 8
% 16.55/8.08  
% 16.55/8.08  #Partial instantiations: 0
% 16.55/8.08  #Strategies tried      : 1
% 16.55/8.08  
% 16.55/8.08  Timing (in seconds)
% 16.55/8.08  ----------------------
% 16.55/8.08  Preprocessing        : 0.26
% 16.55/8.08  Parsing              : 0.14
% 16.55/8.08  CNF conversion       : 0.01
% 16.55/8.08  Main loop            : 7.07
% 16.55/8.08  Inferencing          : 0.92
% 16.55/8.09  Reduction            : 5.14
% 16.55/8.09  Demodulation         : 4.89
% 16.55/8.09  BG Simplification    : 0.16
% 16.55/8.09  Subsumption          : 0.67
% 16.55/8.09  Abstraction          : 0.30
% 16.55/8.09  MUC search           : 0.00
% 16.55/8.09  Cooper               : 0.00
% 16.55/8.09  Total                : 7.35
% 16.55/8.09  Index Insertion      : 0.00
% 16.55/8.09  Index Deletion       : 0.00
% 16.55/8.09  Index Matching       : 0.00
% 16.55/8.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
