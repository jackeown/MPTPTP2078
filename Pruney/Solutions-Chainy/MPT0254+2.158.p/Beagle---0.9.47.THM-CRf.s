%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  59 expanded)
%              Number of equality atoms :   38 (  58 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_314,plain,(
    ! [A_74,B_75,C_76] : k5_xboole_0(k5_xboole_0(A_74,B_75),C_76) = k5_xboole_0(A_74,k5_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_468,plain,(
    ! [A_80,C_81] : k5_xboole_0(A_80,k5_xboole_0(A_80,C_81)) = k5_xboole_0(k1_xboole_0,C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_314])).

tff(c_533,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_468])).

tff(c_551,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_533])).

tff(c_36,plain,(
    ! [A_47] : k3_tarski(k1_tarski(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_113])).

tff(c_125,plain,(
    ! [A_15] : k2_xboole_0(A_15,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_553,plain,(
    ! [A_82,B_83] : k5_xboole_0(k5_xboole_0(A_82,B_83),k2_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_605,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_9,A_9)) = k3_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_553])).

tff(c_612,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k3_xboole_0(A_9,A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_605])).

tff(c_680,plain,(
    ! [A_85] : k3_xboole_0(A_85,A_85) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_612])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_686,plain,(
    ! [A_85] : k5_xboole_0(A_85,A_85) = k4_xboole_0(A_85,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_2])).

tff(c_691,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_686])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [A_52,B_53] :
      ( k1_xboole_0 = A_52
      | k2_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_147,plain,(
    ! [B_59] : k4_xboole_0(k1_tarski(B_59),k1_tarski(B_59)) != k1_tarski(B_59) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_147])).

tff(c_154,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_150])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.39  
% 2.44/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.39  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.44/1.39  
% 2.44/1.39  %Foreground sorts:
% 2.44/1.39  
% 2.44/1.39  
% 2.44/1.39  %Background operators:
% 2.44/1.39  
% 2.44/1.39  
% 2.44/1.39  %Foreground operators:
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.39  
% 2.44/1.41  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.44/1.41  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.44/1.41  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.44/1.41  tff(f_64, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.44/1.41  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.41  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.44/1.41  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.44/1.41  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.44/1.41  tff(f_68, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.44/1.41  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.44/1.41  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.44/1.41  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.41  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.41  tff(c_314, plain, (![A_74, B_75, C_76]: (k5_xboole_0(k5_xboole_0(A_74, B_75), C_76)=k5_xboole_0(A_74, k5_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.41  tff(c_468, plain, (![A_80, C_81]: (k5_xboole_0(A_80, k5_xboole_0(A_80, C_81))=k5_xboole_0(k1_xboole_0, C_81))), inference(superposition, [status(thm), theory('equality')], [c_10, c_314])).
% 2.44/1.41  tff(c_533, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_468])).
% 2.44/1.41  tff(c_551, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_533])).
% 2.44/1.41  tff(c_36, plain, (![A_47]: (k3_tarski(k1_tarski(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.41  tff(c_16, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.41  tff(c_113, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.44/1.41  tff(c_122, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_113])).
% 2.44/1.41  tff(c_125, plain, (![A_15]: (k2_xboole_0(A_15, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_122])).
% 2.44/1.41  tff(c_553, plain, (![A_82, B_83]: (k5_xboole_0(k5_xboole_0(A_82, B_83), k2_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.41  tff(c_605, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_9, A_9))=k3_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_553])).
% 2.44/1.41  tff(c_612, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k3_xboole_0(A_9, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_605])).
% 2.44/1.41  tff(c_680, plain, (![A_85]: (k3_xboole_0(A_85, A_85)=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_551, c_612])).
% 2.44/1.41  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.41  tff(c_686, plain, (![A_85]: (k5_xboole_0(A_85, A_85)=k4_xboole_0(A_85, A_85))), inference(superposition, [status(thm), theory('equality')], [c_680, c_2])).
% 2.44/1.41  tff(c_691, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_686])).
% 2.44/1.41  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.41  tff(c_87, plain, (![A_52, B_53]: (k1_xboole_0=A_52 | k2_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.41  tff(c_91, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_87])).
% 2.44/1.41  tff(c_147, plain, (![B_59]: (k4_xboole_0(k1_tarski(B_59), k1_tarski(B_59))!=k1_tarski(B_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.41  tff(c_150, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_91, c_147])).
% 2.44/1.41  tff(c_154, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_150])).
% 2.44/1.41  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_691, c_154])).
% 2.44/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.41  
% 2.44/1.41  Inference rules
% 2.44/1.41  ----------------------
% 2.44/1.41  #Ref     : 0
% 2.44/1.41  #Sup     : 159
% 2.44/1.41  #Fact    : 0
% 2.44/1.41  #Define  : 0
% 2.44/1.41  #Split   : 0
% 2.44/1.41  #Chain   : 0
% 2.44/1.41  #Close   : 0
% 2.44/1.41  
% 2.44/1.41  Ordering : KBO
% 2.44/1.41  
% 2.44/1.41  Simplification rules
% 2.44/1.41  ----------------------
% 2.44/1.41  #Subsume      : 1
% 2.44/1.41  #Demod        : 89
% 2.44/1.41  #Tautology    : 105
% 2.44/1.41  #SimpNegUnit  : 2
% 2.44/1.41  #BackRed      : 5
% 2.44/1.41  
% 2.44/1.41  #Partial instantiations: 0
% 2.44/1.41  #Strategies tried      : 1
% 2.44/1.41  
% 2.44/1.41  Timing (in seconds)
% 2.44/1.41  ----------------------
% 2.44/1.41  Preprocessing        : 0.31
% 2.44/1.41  Parsing              : 0.16
% 2.44/1.41  CNF conversion       : 0.02
% 2.44/1.41  Main loop            : 0.30
% 2.44/1.41  Inferencing          : 0.10
% 2.44/1.41  Reduction            : 0.11
% 2.44/1.41  Demodulation         : 0.09
% 2.44/1.41  BG Simplification    : 0.02
% 2.44/1.41  Subsumption          : 0.04
% 2.44/1.41  Abstraction          : 0.02
% 2.44/1.41  MUC search           : 0.00
% 2.44/1.41  Cooper               : 0.00
% 2.44/1.41  Total                : 0.65
% 2.44/1.41  Index Insertion      : 0.00
% 2.44/1.41  Index Deletion       : 0.00
% 2.44/1.41  Index Matching       : 0.00
% 2.44/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
