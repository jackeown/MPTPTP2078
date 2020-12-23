%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 149 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 ( 132 expanded)
%              Number of equality atoms :   38 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_195,plain,(
    ! [A_67] : k5_xboole_0(A_67,k1_xboole_0) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_4])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_364,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_572,plain,(
    ! [C_93,A_94,B_95] : k5_xboole_0(C_93,k5_xboole_0(A_94,B_95)) = k5_xboole_0(A_94,k5_xboole_0(B_95,C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_4])).

tff(c_758,plain,(
    ! [A_96,C_97] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_96,C_97)) = k5_xboole_0(C_97,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_572])).

tff(c_823,plain,(
    ! [B_15,A_14] : k5_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_758])).

tff(c_847,plain,(
    ! [B_15,A_14] : k5_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_823])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_218,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_805,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_758])).

tff(c_843,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_805])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2531,plain,(
    ! [A_134,B_135,C_136] : k5_xboole_0(A_134,k5_xboole_0(k3_xboole_0(A_134,B_135),C_136)) = k5_xboole_0(k4_xboole_0(A_134,B_135),C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_364])).

tff(c_2647,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_2531])).

tff(c_2735,plain,(
    ! [B_137,A_138] : k2_xboole_0(B_137,A_138) = k2_xboole_0(A_138,B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_18,c_2647])).

tff(c_34,plain,(
    ! [A_44,B_45] : r1_tarski(k1_tarski(A_44),k2_tarski(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_44,B_45] : k4_xboole_0(k1_tarski(A_44),k2_tarski(A_44,B_45)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_941,plain,(
    ! [B_106,A_107] : k5_xboole_0(k4_xboole_0(B_106,A_107),A_107) = k2_xboole_0(A_107,B_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_823])).

tff(c_995,plain,(
    ! [A_44,B_45] : k2_xboole_0(k2_tarski(A_44,B_45),k1_tarski(A_44)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_941])).

tff(c_1020,plain,(
    ! [A_44,B_45] : k2_xboole_0(k2_tarski(A_44,B_45),k1_tarski(A_44)) = k2_tarski(A_44,B_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_995])).

tff(c_2750,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),k2_tarski(A_44,B_45)) = k2_tarski(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_2735,c_1020])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2750,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:05:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.96  
% 4.99/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.97  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.99/1.97  
% 4.99/1.97  %Foreground sorts:
% 4.99/1.97  
% 4.99/1.97  
% 4.99/1.97  %Background operators:
% 4.99/1.97  
% 4.99/1.97  
% 4.99/1.97  %Foreground operators:
% 4.99/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.99/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.99/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.99/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.99/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.99/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.99/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.99/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.99/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.99/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.99/1.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.99/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.99/1.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.97  
% 4.99/1.98  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.99/1.98  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.99/1.98  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.99/1.98  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.99/1.98  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.99/1.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.99/1.98  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.99/1.98  tff(f_59, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 4.99/1.98  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.99/1.98  tff(f_62, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 4.99/1.98  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.99/1.98  tff(c_14, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/1.98  tff(c_174, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.99/1.98  tff(c_189, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_174])).
% 4.99/1.98  tff(c_195, plain, (![A_67]: (k5_xboole_0(A_67, k1_xboole_0)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_189])).
% 4.99/1.98  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/1.98  tff(c_201, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, A_67)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_195, c_4])).
% 4.99/1.98  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.99/1.98  tff(c_364, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.99/1.98  tff(c_572, plain, (![C_93, A_94, B_95]: (k5_xboole_0(C_93, k5_xboole_0(A_94, B_95))=k5_xboole_0(A_94, k5_xboole_0(B_95, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_364, c_4])).
% 4.99/1.98  tff(c_758, plain, (![A_96, C_97]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_96, C_97))=k5_xboole_0(C_97, A_96))), inference(superposition, [status(thm), theory('equality')], [c_201, c_572])).
% 4.99/1.98  tff(c_823, plain, (![B_15, A_14]: (k5_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_758])).
% 4.99/1.98  tff(c_847, plain, (![B_15, A_14]: (k5_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_823])).
% 4.99/1.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.99/1.98  tff(c_218, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.99/1.98  tff(c_227, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_218])).
% 4.99/1.98  tff(c_805, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_758])).
% 4.99/1.98  tff(c_843, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_805])).
% 4.99/1.98  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.99/1.98  tff(c_2531, plain, (![A_134, B_135, C_136]: (k5_xboole_0(A_134, k5_xboole_0(k3_xboole_0(A_134, B_135), C_136))=k5_xboole_0(k4_xboole_0(A_134, B_135), C_136))), inference(superposition, [status(thm), theory('equality')], [c_10, c_364])).
% 4.99/1.98  tff(c_2647, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_843, c_2531])).
% 4.99/1.98  tff(c_2735, plain, (![B_137, A_138]: (k2_xboole_0(B_137, A_138)=k2_xboole_0(A_138, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_847, c_18, c_2647])).
% 4.99/1.98  tff(c_34, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), k2_tarski(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.99/1.98  tff(c_143, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.99/1.98  tff(c_155, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), k2_tarski(A_44, B_45))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_143])).
% 4.99/1.98  tff(c_941, plain, (![B_106, A_107]: (k5_xboole_0(k4_xboole_0(B_106, A_107), A_107)=k2_xboole_0(A_107, B_106))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_823])).
% 4.99/1.98  tff(c_995, plain, (![A_44, B_45]: (k2_xboole_0(k2_tarski(A_44, B_45), k1_tarski(A_44))=k5_xboole_0(k1_xboole_0, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_941])).
% 4.99/1.98  tff(c_1020, plain, (![A_44, B_45]: (k2_xboole_0(k2_tarski(A_44, B_45), k1_tarski(A_44))=k2_tarski(A_44, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_995])).
% 4.99/1.98  tff(c_2750, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), k2_tarski(A_44, B_45))=k2_tarski(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_2735, c_1020])).
% 4.99/1.98  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.99/1.98  tff(c_2818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2750, c_36])).
% 4.99/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.98  
% 4.99/1.98  Inference rules
% 4.99/1.98  ----------------------
% 4.99/1.98  #Ref     : 0
% 4.99/1.98  #Sup     : 701
% 4.99/1.98  #Fact    : 0
% 4.99/1.98  #Define  : 0
% 4.99/1.98  #Split   : 0
% 4.99/1.98  #Chain   : 0
% 4.99/1.98  #Close   : 0
% 4.99/1.98  
% 4.99/1.98  Ordering : KBO
% 4.99/1.98  
% 4.99/1.98  Simplification rules
% 4.99/1.98  ----------------------
% 4.99/1.98  #Subsume      : 88
% 4.99/1.98  #Demod        : 418
% 4.99/1.98  #Tautology    : 255
% 4.99/1.98  #SimpNegUnit  : 0
% 4.99/1.98  #BackRed      : 1
% 4.99/1.98  
% 4.99/1.98  #Partial instantiations: 0
% 4.99/1.98  #Strategies tried      : 1
% 4.99/1.98  
% 4.99/1.98  Timing (in seconds)
% 4.99/1.98  ----------------------
% 4.99/1.98  Preprocessing        : 0.31
% 4.99/1.98  Parsing              : 0.16
% 4.99/1.98  CNF conversion       : 0.02
% 4.99/1.98  Main loop            : 0.91
% 4.99/1.98  Inferencing          : 0.24
% 4.99/1.98  Reduction            : 0.50
% 4.99/1.98  Demodulation         : 0.45
% 4.99/1.98  BG Simplification    : 0.04
% 4.99/1.98  Subsumption          : 0.10
% 4.99/1.98  Abstraction          : 0.05
% 4.99/1.98  MUC search           : 0.00
% 4.99/1.98  Cooper               : 0.00
% 4.99/1.98  Total                : 1.25
% 4.99/1.98  Index Insertion      : 0.00
% 4.99/1.98  Index Deletion       : 0.00
% 4.99/1.98  Index Matching       : 0.00
% 4.99/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
