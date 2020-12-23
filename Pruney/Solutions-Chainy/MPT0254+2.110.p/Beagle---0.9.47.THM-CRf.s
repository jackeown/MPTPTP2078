%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:33 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  61 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_281,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_258])).

tff(c_284,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_281])).

tff(c_36,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    ! [B_49] : k1_tarski(B_49) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_36])).

tff(c_89,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,A_55) = k5_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_55] : k5_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_615,plain,(
    ! [A_87,B_88] : k5_xboole_0(k5_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_679,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_615])).

tff(c_689,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_16,c_679])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_271,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_627,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k5_xboole_0(B_88,k3_xboole_0(A_87,B_88))) = k2_xboole_0(A_87,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_14])).

tff(c_1226,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k4_xboole_0(B_125,A_124)) = k2_xboole_0(A_124,B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_627])).

tff(c_526,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_601,plain,(
    ! [A_15,C_86] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_86)) = k5_xboole_0(k1_xboole_0,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_526])).

tff(c_614,plain,(
    ! [A_15,C_86] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_601])).

tff(c_1737,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k2_xboole_0(A_134,B_135)) = k4_xboole_0(B_135,A_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_614])).

tff(c_1792,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k4_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1737])).

tff(c_1802,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1792])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1809,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1802,c_10])).

tff(c_1813,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_40,c_1809])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_1813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:36:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.48  
% 3.34/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.48  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.34/1.48  
% 3.34/1.48  %Foreground sorts:
% 3.34/1.48  
% 3.34/1.48  
% 3.34/1.48  %Background operators:
% 3.34/1.48  
% 3.34/1.48  
% 3.34/1.48  %Foreground operators:
% 3.34/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.34/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.48  
% 3.34/1.50  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.34/1.50  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.34/1.50  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.50  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.34/1.50  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.34/1.50  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.50  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.34/1.50  tff(f_68, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.34/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.50  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.34/1.50  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.34/1.50  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.50  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.50  tff(c_258, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.50  tff(c_281, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_258])).
% 3.34/1.50  tff(c_284, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_281])).
% 3.34/1.50  tff(c_36, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.50  tff(c_285, plain, (![B_49]: (k1_tarski(B_49)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_36])).
% 3.34/1.50  tff(c_89, plain, (![B_54, A_55]: (k5_xboole_0(B_54, A_55)=k5_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.50  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.50  tff(c_105, plain, (![A_55]: (k5_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 3.34/1.50  tff(c_615, plain, (![A_87, B_88]: (k5_xboole_0(k5_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.50  tff(c_679, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_615])).
% 3.34/1.50  tff(c_689, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_16, c_679])).
% 3.34/1.50  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.50  tff(c_271, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_258])).
% 3.34/1.50  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.50  tff(c_627, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k5_xboole_0(B_88, k3_xboole_0(A_87, B_88)))=k2_xboole_0(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_615, c_14])).
% 3.34/1.50  tff(c_1226, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k4_xboole_0(B_125, A_124))=k2_xboole_0(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_627])).
% 3.34/1.50  tff(c_526, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.50  tff(c_601, plain, (![A_15, C_86]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_86))=k5_xboole_0(k1_xboole_0, C_86))), inference(superposition, [status(thm), theory('equality')], [c_16, c_526])).
% 3.34/1.50  tff(c_614, plain, (![A_15, C_86]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_601])).
% 3.34/1.50  tff(c_1737, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k2_xboole_0(A_134, B_135))=k4_xboole_0(B_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_614])).
% 3.34/1.50  tff(c_1792, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k4_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1737])).
% 3.34/1.50  tff(c_1802, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1792])).
% 3.34/1.50  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.50  tff(c_1809, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1802, c_10])).
% 3.34/1.50  tff(c_1813, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_689, c_40, c_1809])).
% 3.34/1.50  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_1813])).
% 3.34/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.50  
% 3.34/1.50  Inference rules
% 3.34/1.50  ----------------------
% 3.34/1.50  #Ref     : 0
% 3.34/1.50  #Sup     : 419
% 3.34/1.50  #Fact    : 0
% 3.34/1.50  #Define  : 0
% 3.34/1.50  #Split   : 0
% 3.34/1.50  #Chain   : 0
% 3.34/1.50  #Close   : 0
% 3.34/1.50  
% 3.34/1.50  Ordering : KBO
% 3.34/1.50  
% 3.34/1.50  Simplification rules
% 3.34/1.50  ----------------------
% 3.34/1.50  #Subsume      : 12
% 3.34/1.50  #Demod        : 248
% 3.34/1.50  #Tautology    : 310
% 3.34/1.50  #SimpNegUnit  : 3
% 3.34/1.50  #BackRed      : 13
% 3.34/1.50  
% 3.34/1.50  #Partial instantiations: 0
% 3.34/1.50  #Strategies tried      : 1
% 3.34/1.50  
% 3.34/1.50  Timing (in seconds)
% 3.34/1.50  ----------------------
% 3.34/1.50  Preprocessing        : 0.32
% 3.34/1.50  Parsing              : 0.17
% 3.34/1.50  CNF conversion       : 0.02
% 3.34/1.50  Main loop            : 0.44
% 3.34/1.50  Inferencing          : 0.16
% 3.34/1.50  Reduction            : 0.18
% 3.34/1.50  Demodulation         : 0.15
% 3.34/1.50  BG Simplification    : 0.02
% 3.34/1.50  Subsumption          : 0.06
% 3.34/1.50  Abstraction          : 0.03
% 3.34/1.50  MUC search           : 0.00
% 3.34/1.50  Cooper               : 0.00
% 3.34/1.50  Total                : 0.79
% 3.34/1.50  Index Insertion      : 0.00
% 3.34/1.50  Index Deletion       : 0.00
% 3.34/1.50  Index Matching       : 0.00
% 3.34/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
