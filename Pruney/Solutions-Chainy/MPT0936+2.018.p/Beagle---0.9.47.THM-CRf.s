%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   48 (  96 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  91 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_16,plain,(
    ! [A_24] : k3_tarski(k1_tarski(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_1] : k3_tarski(k1_tarski(A_1)) = k2_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_63,plain,(
    ! [A_41] : k2_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_22,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_22])).

tff(c_157,plain,(
    ! [A_63,B_64,C_65] : k2_zfmisc_1(k1_tarski(A_63),k2_tarski(B_64,C_65)) = k2_tarski(k4_tarski(A_63,B_64),k4_tarski(A_63,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_179,plain,(
    ! [A_63,C_65] : k2_zfmisc_1(k1_tarski(A_63),k2_tarski(C_65,C_65)) = k1_tarski(k4_tarski(A_63,C_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_213,plain,(
    ! [A_66,C_67] : k2_zfmisc_1(k1_tarski(A_66),k1_tarski(C_67)) = k1_tarski(k4_tarski(A_66,C_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k2_zfmisc_1(A_30,B_31)) = A_30
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_66,C_67] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_66,C_67))) = k1_tarski(A_66)
      | k1_tarski(C_67) = k1_xboole_0
      | k1_tarski(A_66) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_26])).

tff(c_228,plain,(
    ! [A_66,C_67] : k1_relat_1(k1_tarski(k4_tarski(A_66,C_67))) = k1_tarski(A_66) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_222])).

tff(c_28,plain,(
    ! [A_32,B_33,C_34] : k4_tarski(k4_tarski(A_32,B_33),C_34) = k3_mcart_1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_70,C_71] : k1_relat_1(k1_tarski(k4_tarski(A_70,C_71))) = k1_tarski(A_70) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_222])).

tff(c_251,plain,(
    ! [A_32,B_33,C_34] : k1_relat_1(k1_tarski(k3_mcart_1(A_32,B_33,C_34))) = k1_tarski(k4_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_242])).

tff(c_30,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_278,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_30])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.25  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.15/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_41, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.15/1.26  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.26  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.15/1.26  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.15/1.26  tff(f_45, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.15/1.26  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.15/1.26  tff(f_62, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.15/1.26  tff(f_65, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.15/1.26  tff(c_16, plain, (![A_24]: (k3_tarski(k1_tarski(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.26  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.26  tff(c_50, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.26  tff(c_59, plain, (![A_1]: (k3_tarski(k1_tarski(A_1))=k2_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_50])).
% 2.15/1.26  tff(c_63, plain, (![A_41]: (k2_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_59])).
% 2.15/1.26  tff(c_22, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.26  tff(c_70, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_22])).
% 2.15/1.26  tff(c_157, plain, (![A_63, B_64, C_65]: (k2_zfmisc_1(k1_tarski(A_63), k2_tarski(B_64, C_65))=k2_tarski(k4_tarski(A_63, B_64), k4_tarski(A_63, C_65)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.26  tff(c_179, plain, (![A_63, C_65]: (k2_zfmisc_1(k1_tarski(A_63), k2_tarski(C_65, C_65))=k1_tarski(k4_tarski(A_63, C_65)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 2.15/1.26  tff(c_213, plain, (![A_66, C_67]: (k2_zfmisc_1(k1_tarski(A_66), k1_tarski(C_67))=k1_tarski(k4_tarski(A_66, C_67)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_179])).
% 2.15/1.26  tff(c_26, plain, (![A_30, B_31]: (k1_relat_1(k2_zfmisc_1(A_30, B_31))=A_30 | k1_xboole_0=B_31 | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.26  tff(c_222, plain, (![A_66, C_67]: (k1_relat_1(k1_tarski(k4_tarski(A_66, C_67)))=k1_tarski(A_66) | k1_tarski(C_67)=k1_xboole_0 | k1_tarski(A_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_213, c_26])).
% 2.15/1.26  tff(c_228, plain, (![A_66, C_67]: (k1_relat_1(k1_tarski(k4_tarski(A_66, C_67)))=k1_tarski(A_66))), inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_222])).
% 2.15/1.26  tff(c_28, plain, (![A_32, B_33, C_34]: (k4_tarski(k4_tarski(A_32, B_33), C_34)=k3_mcart_1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.26  tff(c_242, plain, (![A_70, C_71]: (k1_relat_1(k1_tarski(k4_tarski(A_70, C_71)))=k1_tarski(A_70))), inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_222])).
% 2.15/1.26  tff(c_251, plain, (![A_32, B_33, C_34]: (k1_relat_1(k1_tarski(k3_mcart_1(A_32, B_33, C_34)))=k1_tarski(k4_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_242])).
% 2.15/1.26  tff(c_30, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.26  tff(c_278, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_30])).
% 2.15/1.26  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_278])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 56
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 0
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 0
% 2.15/1.26  #Demod        : 14
% 2.15/1.26  #Tautology    : 41
% 2.15/1.26  #SimpNegUnit  : 4
% 2.15/1.26  #BackRed      : 1
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.30
% 2.15/1.26  Parsing              : 0.15
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.17
% 2.15/1.26  Inferencing          : 0.07
% 2.15/1.26  Reduction            : 0.06
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.02
% 2.15/1.26  Subsumption          : 0.02
% 2.15/1.26  Abstraction          : 0.02
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.49
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
