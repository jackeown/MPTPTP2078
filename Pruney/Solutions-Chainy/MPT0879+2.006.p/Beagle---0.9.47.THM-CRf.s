%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  67 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  50 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_117,plain,(
    ! [A_58,B_59,C_60,D_61] : k4_tarski(k3_mcart_1(A_58,B_59,C_60),D_61) = k4_mcart_1(A_58,B_59,C_60,D_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_40,B_41] : k1_mcart_1(k4_tarski(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [A_58,B_59,C_60,D_61] : k1_mcart_1(k4_mcart_1(A_58,B_59,C_60,D_61)) = k3_mcart_1(A_58,B_59,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_26])).

tff(c_159,plain,(
    ! [A_74,B_75,C_76,D_77] : k4_tarski(k4_tarski(k4_tarski(A_74,B_75),C_76),D_77) = k4_mcart_1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_171,plain,(
    ! [A_74,B_75,C_76,D_77] : k4_tarski(k4_tarski(A_74,B_75),C_76) = k1_mcart_1(k4_mcart_1(A_74,B_75,C_76,D_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_26])).

tff(c_188,plain,(
    ! [A_74,B_75,C_76] : k4_tarski(k4_tarski(A_74,B_75),C_76) = k3_mcart_1(A_74,B_75,C_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_171])).

tff(c_58,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_19] : k1_enumset1(A_19,A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [B_48] : k2_tarski(B_48,B_48) = k1_tarski(B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_10])).

tff(c_191,plain,(
    ! [A_78,B_79,C_80] : k2_zfmisc_1(k2_tarski(A_78,B_79),k1_tarski(C_80)) = k2_tarski(k4_tarski(A_78,C_80),k4_tarski(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_235,plain,(
    ! [A_78,C_80] : k2_zfmisc_1(k2_tarski(A_78,A_78),k1_tarski(C_80)) = k1_tarski(k4_tarski(A_78,C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_191])).

tff(c_244,plain,(
    ! [A_78,C_80] : k2_zfmisc_1(k1_tarski(A_78),k1_tarski(C_80)) = k1_tarski(k4_tarski(A_78,C_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_235])).

tff(c_370,plain,(
    ! [A_93,C_94] : k2_zfmisc_1(k1_tarski(A_93),k1_tarski(C_94)) = k1_tarski(k4_tarski(A_93,C_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_235])).

tff(c_20,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_376,plain,(
    ! [A_93,C_94,C_31] : k3_zfmisc_1(k1_tarski(A_93),k1_tarski(C_94),C_31) = k2_zfmisc_1(k1_tarski(k4_tarski(A_93,C_94)),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_20])).

tff(c_30,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_455,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_30])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_244,c_455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:42:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.35/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.35/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.35/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.35/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.35/1.33  
% 2.35/1.34  tff(f_47, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.35/1.34  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.35/1.34  tff(f_49, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.35/1.34  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.35/1.34  tff(f_35, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.35/1.34  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.35/1.34  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.35/1.34  tff(f_56, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 2.35/1.34  tff(c_117, plain, (![A_58, B_59, C_60, D_61]: (k4_tarski(k3_mcart_1(A_58, B_59, C_60), D_61)=k4_mcart_1(A_58, B_59, C_60, D_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.34  tff(c_26, plain, (![A_40, B_41]: (k1_mcart_1(k4_tarski(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.34  tff(c_123, plain, (![A_58, B_59, C_60, D_61]: (k1_mcart_1(k4_mcart_1(A_58, B_59, C_60, D_61))=k3_mcart_1(A_58, B_59, C_60))), inference(superposition, [status(thm), theory('equality')], [c_117, c_26])).
% 2.35/1.34  tff(c_159, plain, (![A_74, B_75, C_76, D_77]: (k4_tarski(k4_tarski(k4_tarski(A_74, B_75), C_76), D_77)=k4_mcart_1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.34  tff(c_171, plain, (![A_74, B_75, C_76, D_77]: (k4_tarski(k4_tarski(A_74, B_75), C_76)=k1_mcart_1(k4_mcart_1(A_74, B_75, C_76, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_26])).
% 2.35/1.34  tff(c_188, plain, (![A_74, B_75, C_76]: (k4_tarski(k4_tarski(A_74, B_75), C_76)=k3_mcart_1(A_74, B_75, C_76))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_171])).
% 2.35/1.34  tff(c_58, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.34  tff(c_10, plain, (![A_19]: (k1_enumset1(A_19, A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.34  tff(c_65, plain, (![B_48]: (k2_tarski(B_48, B_48)=k1_tarski(B_48))), inference(superposition, [status(thm), theory('equality')], [c_58, c_10])).
% 2.35/1.34  tff(c_191, plain, (![A_78, B_79, C_80]: (k2_zfmisc_1(k2_tarski(A_78, B_79), k1_tarski(C_80))=k2_tarski(k4_tarski(A_78, C_80), k4_tarski(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.34  tff(c_235, plain, (![A_78, C_80]: (k2_zfmisc_1(k2_tarski(A_78, A_78), k1_tarski(C_80))=k1_tarski(k4_tarski(A_78, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_191])).
% 2.35/1.34  tff(c_244, plain, (![A_78, C_80]: (k2_zfmisc_1(k1_tarski(A_78), k1_tarski(C_80))=k1_tarski(k4_tarski(A_78, C_80)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_235])).
% 2.35/1.34  tff(c_370, plain, (![A_93, C_94]: (k2_zfmisc_1(k1_tarski(A_93), k1_tarski(C_94))=k1_tarski(k4_tarski(A_93, C_94)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_235])).
% 2.35/1.34  tff(c_20, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.34  tff(c_376, plain, (![A_93, C_94, C_31]: (k3_zfmisc_1(k1_tarski(A_93), k1_tarski(C_94), C_31)=k2_zfmisc_1(k1_tarski(k4_tarski(A_93, C_94)), C_31))), inference(superposition, [status(thm), theory('equality')], [c_370, c_20])).
% 2.35/1.34  tff(c_30, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.34  tff(c_455, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_30])).
% 2.35/1.34  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_244, c_455])).
% 2.35/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  Inference rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Ref     : 0
% 2.35/1.34  #Sup     : 104
% 2.35/1.34  #Fact    : 0
% 2.35/1.34  #Define  : 0
% 2.35/1.34  #Split   : 0
% 2.35/1.34  #Chain   : 0
% 2.35/1.34  #Close   : 0
% 2.35/1.34  
% 2.35/1.34  Ordering : KBO
% 2.35/1.34  
% 2.35/1.34  Simplification rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Subsume      : 0
% 2.35/1.34  #Demod        : 41
% 2.35/1.34  #Tautology    : 65
% 2.35/1.34  #SimpNegUnit  : 0
% 2.35/1.34  #BackRed      : 2
% 2.35/1.34  
% 2.35/1.34  #Partial instantiations: 0
% 2.35/1.34  #Strategies tried      : 1
% 2.35/1.34  
% 2.35/1.34  Timing (in seconds)
% 2.35/1.34  ----------------------
% 2.35/1.34  Preprocessing        : 0.33
% 2.35/1.34  Parsing              : 0.18
% 2.35/1.34  CNF conversion       : 0.02
% 2.35/1.34  Main loop            : 0.23
% 2.35/1.34  Inferencing          : 0.10
% 2.35/1.34  Reduction            : 0.08
% 2.35/1.34  Demodulation         : 0.06
% 2.35/1.34  BG Simplification    : 0.02
% 2.35/1.34  Subsumption          : 0.02
% 2.35/1.34  Abstraction          : 0.02
% 2.35/1.34  MUC search           : 0.00
% 2.35/1.34  Cooper               : 0.00
% 2.35/1.34  Total                : 0.59
% 2.35/1.34  Index Insertion      : 0.00
% 2.35/1.34  Index Deletion       : 0.00
% 2.35/1.34  Index Matching       : 0.00
% 2.35/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
