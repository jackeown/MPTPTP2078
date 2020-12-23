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
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 42.48s
% Output     : CNFRefutation 42.65s
% Verified   : 
% Statistics : Number of formulae       :   59 (  94 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  89 expanded)
%              Number of equality atoms :   46 (  88 expanded)
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

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_247,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_904,plain,(
    ! [A_97,C_98] : k5_xboole_0(A_97,k5_xboole_0(A_97,C_98)) = k5_xboole_0(k1_xboole_0,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_247])).

tff(c_1015,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_904])).

tff(c_1040,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1015])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_359,plain,(
    ! [A_76,B_77] : k5_xboole_0(k5_xboole_0(A_76,B_77),k3_xboole_0(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_405,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_359])).

tff(c_418,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k2_xboole_0(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_405])).

tff(c_1055,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_418])).

tff(c_16,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(k1_tarski(A_44),k1_tarski(B_45)) = k1_tarski(A_44)
      | B_45 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_156,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k5_xboole_0(B_77,k3_xboole_0(A_76,B_77))) = k2_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_10])).

tff(c_1586,plain,(
    ! [A_125,B_126] : k5_xboole_0(A_125,k4_xboole_0(B_126,A_125)) = k2_xboole_0(A_125,B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_374])).

tff(c_36252,plain,(
    ! [B_343,A_344] :
      ( k5_xboole_0(k1_tarski(B_343),k1_tarski(A_344)) = k2_xboole_0(k1_tarski(B_343),k1_tarski(A_344))
      | B_343 = A_344 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1586])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( k5_xboole_0(k1_tarski(A_46),k1_tarski(B_47)) = k2_tarski(A_46,B_47)
      | B_47 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131615,plain,(
    ! [B_558,A_559] :
      ( k2_xboole_0(k1_tarski(B_558),k1_tarski(A_559)) = k2_tarski(B_558,A_559)
      | B_558 = A_559
      | B_558 = A_559 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36252,c_36])).

tff(c_30,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_131758,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_131615,c_39])).

tff(c_131762,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131758,c_131758,c_39])).

tff(c_131765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_16,c_131762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.48/33.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.48/33.97  
% 42.48/33.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.61/33.97  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 42.61/33.97  
% 42.61/33.97  %Foreground sorts:
% 42.61/33.97  
% 42.61/33.97  
% 42.61/33.97  %Background operators:
% 42.61/33.97  
% 42.61/33.97  
% 42.61/33.97  %Foreground operators:
% 42.61/33.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.61/33.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 42.61/33.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.61/33.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 42.61/33.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 42.61/33.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 42.61/33.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 42.61/33.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 42.61/33.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 42.61/33.97  tff('#skF_2', type, '#skF_2': $i).
% 42.61/33.97  tff('#skF_1', type, '#skF_1': $i).
% 42.61/33.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 42.61/33.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 42.61/33.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.61/33.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 42.61/33.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.61/33.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.61/33.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 42.61/33.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 42.61/33.97  
% 42.65/33.98  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 42.65/33.98  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 42.65/33.98  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 42.65/33.98  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 42.65/33.98  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 42.65/33.98  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 42.65/33.98  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 42.65/33.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 42.65/33.98  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 42.65/33.98  tff(f_65, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 42.65/33.98  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 42.65/33.98  tff(f_68, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 42.65/33.98  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.65/33.98  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 42.65/33.98  tff(c_247, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.65/33.98  tff(c_904, plain, (![A_97, C_98]: (k5_xboole_0(A_97, k5_xboole_0(A_97, C_98))=k5_xboole_0(k1_xboole_0, C_98))), inference(superposition, [status(thm), theory('equality')], [c_12, c_247])).
% 42.65/33.98  tff(c_1015, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_904])).
% 42.65/33.98  tff(c_1040, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1015])).
% 42.65/33.98  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 42.65/33.98  tff(c_359, plain, (![A_76, B_77]: (k5_xboole_0(k5_xboole_0(A_76, B_77), k3_xboole_0(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 42.65/33.98  tff(c_405, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_359])).
% 42.65/33.98  tff(c_418, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k2_xboole_0(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_405])).
% 42.65/33.98  tff(c_1055, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_418])).
% 42.65/33.98  tff(c_16, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 42.65/33.98  tff(c_34, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), k1_tarski(B_45))=k1_tarski(A_44) | B_45=A_44)), inference(cnfTransformation, [status(thm)], [f_60])).
% 42.65/33.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 42.65/33.98  tff(c_156, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 42.65/33.98  tff(c_168, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 42.65/33.98  tff(c_10, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.65/33.98  tff(c_374, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k5_xboole_0(B_77, k3_xboole_0(A_76, B_77)))=k2_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_359, c_10])).
% 42.65/33.98  tff(c_1586, plain, (![A_125, B_126]: (k5_xboole_0(A_125, k4_xboole_0(B_126, A_125))=k2_xboole_0(A_125, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_374])).
% 42.65/33.98  tff(c_36252, plain, (![B_343, A_344]: (k5_xboole_0(k1_tarski(B_343), k1_tarski(A_344))=k2_xboole_0(k1_tarski(B_343), k1_tarski(A_344)) | B_343=A_344)), inference(superposition, [status(thm), theory('equality')], [c_34, c_1586])).
% 42.65/33.98  tff(c_36, plain, (![A_46, B_47]: (k5_xboole_0(k1_tarski(A_46), k1_tarski(B_47))=k2_tarski(A_46, B_47) | B_47=A_46)), inference(cnfTransformation, [status(thm)], [f_65])).
% 42.65/33.98  tff(c_131615, plain, (![B_558, A_559]: (k2_xboole_0(k1_tarski(B_558), k1_tarski(A_559))=k2_tarski(B_558, A_559) | B_558=A_559 | B_558=A_559)), inference(superposition, [status(thm), theory('equality')], [c_36252, c_36])).
% 42.65/33.98  tff(c_30, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 42.65/33.98  tff(c_38, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 42.65/33.98  tff(c_39, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 42.65/33.98  tff(c_131758, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_131615, c_39])).
% 42.65/33.98  tff(c_131762, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131758, c_131758, c_39])).
% 42.65/33.98  tff(c_131765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1055, c_16, c_131762])).
% 42.65/33.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.65/33.98  
% 42.65/33.98  Inference rules
% 42.65/33.98  ----------------------
% 42.65/33.98  #Ref     : 0
% 42.65/33.98  #Sup     : 34039
% 42.65/33.98  #Fact    : 0
% 42.65/33.98  #Define  : 0
% 42.65/33.98  #Split   : 0
% 42.65/33.98  #Chain   : 0
% 42.65/33.98  #Close   : 0
% 42.65/33.98  
% 42.65/33.98  Ordering : KBO
% 42.65/33.98  
% 42.65/33.98  Simplification rules
% 42.65/33.98  ----------------------
% 42.65/33.98  #Subsume      : 2797
% 42.65/33.98  #Demod        : 45325
% 42.65/33.98  #Tautology    : 10266
% 42.65/33.98  #SimpNegUnit  : 19
% 42.65/33.98  #BackRed      : 15
% 42.65/33.98  
% 42.65/33.98  #Partial instantiations: 0
% 42.65/33.98  #Strategies tried      : 1
% 42.65/33.98  
% 42.65/33.98  Timing (in seconds)
% 42.65/33.98  ----------------------
% 42.65/33.99  Preprocessing        : 0.32
% 42.65/33.99  Parsing              : 0.17
% 42.65/33.99  CNF conversion       : 0.02
% 42.65/33.99  Main loop            : 32.89
% 42.65/33.99  Inferencing          : 2.82
% 42.65/33.99  Reduction            : 24.28
% 42.65/33.99  Demodulation         : 23.29
% 42.65/33.99  BG Simplification    : 0.55
% 42.65/33.99  Subsumption          : 4.35
% 42.65/33.99  Abstraction          : 0.91
% 42.65/33.99  MUC search           : 0.00
% 42.65/33.99  Cooper               : 0.00
% 42.65/33.99  Total                : 33.25
% 42.65/33.99  Index Insertion      : 0.00
% 42.65/33.99  Index Deletion       : 0.00
% 42.65/33.99  Index Matching       : 0.00
% 42.65/33.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
