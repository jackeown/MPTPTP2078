%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 146 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 143 expanded)
%              Number of equality atoms :   45 ( 142 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_216,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_201])).

tff(c_220,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_32,plain,(
    ! [A_26] : k1_setfam_1(k1_tarski(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_167,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_170,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_210,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_201])).

tff(c_238,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_210])).

tff(c_24,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_239,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_24])).

tff(c_348,plain,(
    ! [A_80,B_81,C_82] : k2_zfmisc_1(k2_tarski(A_80,B_81),k1_tarski(C_82)) = k2_tarski(k4_tarski(A_80,C_82),k4_tarski(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_376,plain,(
    ! [B_81,C_82] : k2_zfmisc_1(k2_tarski(B_81,B_81),k1_tarski(C_82)) = k1_tarski(k4_tarski(B_81,C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_8])).

tff(c_411,plain,(
    ! [B_83,C_84] : k2_zfmisc_1(k1_tarski(B_83),k1_tarski(C_84)) = k1_tarski(k4_tarski(B_83,C_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_376])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k2_zfmisc_1(A_29,B_30)) = A_29
      | k1_xboole_0 = B_30
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_420,plain,(
    ! [B_83,C_84] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_83,C_84))) = k1_tarski(B_83)
      | k1_tarski(C_84) = k1_xboole_0
      | k1_tarski(B_83) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_38])).

tff(c_429,plain,(
    ! [B_83,C_84] : k1_relat_1(k1_tarski(k4_tarski(B_83,C_84))) = k1_tarski(B_83) ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_239,c_420])).

tff(c_40,plain,(
    ! [A_31,B_32,C_33] : k4_tarski(k4_tarski(A_31,B_32),C_33) = k3_mcart_1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_444,plain,(
    ! [B_87,C_88] : k1_relat_1(k1_tarski(k4_tarski(B_87,C_88))) = k1_tarski(B_87) ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_239,c_420])).

tff(c_453,plain,(
    ! [A_31,B_32,C_33] : k1_relat_1(k1_tarski(k3_mcart_1(A_31,B_32,C_33))) = k1_tarski(k4_tarski(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_444])).

tff(c_42,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_551,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_42])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  %$ k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.27  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.18/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.28  
% 2.18/1.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.18/1.29  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.18/1.29  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.18/1.29  tff(f_58, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.18/1.29  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.29  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.29  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.18/1.29  tff(f_56, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.18/1.29  tff(f_72, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.18/1.29  tff(f_74, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.18/1.29  tff(f_77, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.18/1.29  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.29  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.29  tff(c_201, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.29  tff(c_216, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_201])).
% 2.18/1.29  tff(c_220, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_216])).
% 2.18/1.29  tff(c_32, plain, (![A_26]: (k1_setfam_1(k1_tarski(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.29  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.29  tff(c_158, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.29  tff(c_167, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 2.18/1.29  tff(c_170, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.18/1.29  tff(c_210, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_170, c_201])).
% 2.18/1.29  tff(c_238, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_210])).
% 2.18/1.29  tff(c_24, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.29  tff(c_239, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_24])).
% 2.18/1.29  tff(c_348, plain, (![A_80, B_81, C_82]: (k2_zfmisc_1(k2_tarski(A_80, B_81), k1_tarski(C_82))=k2_tarski(k4_tarski(A_80, C_82), k4_tarski(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.29  tff(c_376, plain, (![B_81, C_82]: (k2_zfmisc_1(k2_tarski(B_81, B_81), k1_tarski(C_82))=k1_tarski(k4_tarski(B_81, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_8])).
% 2.18/1.29  tff(c_411, plain, (![B_83, C_84]: (k2_zfmisc_1(k1_tarski(B_83), k1_tarski(C_84))=k1_tarski(k4_tarski(B_83, C_84)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_376])).
% 2.18/1.29  tff(c_38, plain, (![A_29, B_30]: (k1_relat_1(k2_zfmisc_1(A_29, B_30))=A_29 | k1_xboole_0=B_30 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.29  tff(c_420, plain, (![B_83, C_84]: (k1_relat_1(k1_tarski(k4_tarski(B_83, C_84)))=k1_tarski(B_83) | k1_tarski(C_84)=k1_xboole_0 | k1_tarski(B_83)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_411, c_38])).
% 2.18/1.29  tff(c_429, plain, (![B_83, C_84]: (k1_relat_1(k1_tarski(k4_tarski(B_83, C_84)))=k1_tarski(B_83))), inference(negUnitSimplification, [status(thm)], [c_239, c_239, c_420])).
% 2.18/1.29  tff(c_40, plain, (![A_31, B_32, C_33]: (k4_tarski(k4_tarski(A_31, B_32), C_33)=k3_mcart_1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.29  tff(c_444, plain, (![B_87, C_88]: (k1_relat_1(k1_tarski(k4_tarski(B_87, C_88)))=k1_tarski(B_87))), inference(negUnitSimplification, [status(thm)], [c_239, c_239, c_420])).
% 2.18/1.29  tff(c_453, plain, (![A_31, B_32, C_33]: (k1_relat_1(k1_tarski(k3_mcart_1(A_31, B_32, C_33)))=k1_tarski(k4_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_444])).
% 2.18/1.29  tff(c_42, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.29  tff(c_551, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_453, c_42])).
% 2.18/1.29  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_551])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 120
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 0
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 1
% 2.18/1.29  #Demod        : 37
% 2.18/1.29  #Tautology    : 87
% 2.18/1.29  #SimpNegUnit  : 11
% 2.18/1.29  #BackRed      : 2
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.30
% 2.18/1.29  Parsing              : 0.16
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.23
% 2.18/1.29  Inferencing          : 0.09
% 2.18/1.29  Reduction            : 0.08
% 2.18/1.29  Demodulation         : 0.06
% 2.18/1.29  BG Simplification    : 0.02
% 2.18/1.29  Subsumption          : 0.03
% 2.18/1.29  Abstraction          : 0.02
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.55
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
