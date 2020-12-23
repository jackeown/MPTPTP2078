%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  38 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_98,plain,(
    ! [A_56,B_57,C_58,D_59] : k4_tarski(k3_mcart_1(A_56,B_57,C_58),D_59) = k4_mcart_1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [A_56,B_57,C_58,D_59] : k1_mcart_1(k4_mcart_1(A_56,B_57,C_58,D_59)) = k3_mcart_1(A_56,B_57,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_24])).

tff(c_131,plain,(
    ! [A_68,B_69,C_70,D_71] : k4_tarski(k4_tarski(k4_tarski(A_68,B_69),C_70),D_71) = k4_mcart_1(A_68,B_69,C_70,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [A_68,B_69,C_70,D_71] : k4_tarski(k4_tarski(A_68,B_69),C_70) = k1_mcart_1(k4_mcart_1(A_68,B_69,C_70,D_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_24])).

tff(c_160,plain,(
    ! [A_68,B_69,C_70] : k4_tarski(k4_tarski(A_68,B_69),C_70) = k3_mcart_1(A_68,B_69,C_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_143])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [A_81,B_82,C_83] : k2_zfmisc_1(k1_tarski(A_81),k2_tarski(B_82,C_83)) = k2_tarski(k4_tarski(A_81,B_82),k4_tarski(A_81,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_225,plain,(
    ! [A_81,C_83] : k2_zfmisc_1(k1_tarski(A_81),k2_tarski(C_83,C_83)) = k1_tarski(k4_tarski(A_81,C_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2])).

tff(c_256,plain,(
    ! [A_81,C_83] : k2_zfmisc_1(k1_tarski(A_81),k1_tarski(C_83)) = k1_tarski(k4_tarski(A_81,C_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_265,plain,(
    ! [A_84,C_85] : k2_zfmisc_1(k1_tarski(A_84),k1_tarski(C_85)) = k1_tarski(k4_tarski(A_84,C_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_18,plain,(
    ! [A_26,B_27,C_28] : k2_zfmisc_1(k2_zfmisc_1(A_26,B_27),C_28) = k3_zfmisc_1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_271,plain,(
    ! [A_84,C_85,C_28] : k3_zfmisc_1(k1_tarski(A_84),k1_tarski(C_85),C_28) = k2_zfmisc_1(k1_tarski(k4_tarski(A_84,C_85)),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_18])).

tff(c_28,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_400,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_28])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_256,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  
% 2.30/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.36  
% 2.30/1.36  %Foreground sorts:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Background operators:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Foreground operators:
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.36  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.30/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.36  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.30/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.30/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.30/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.36  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.30/1.36  
% 2.30/1.37  tff(f_45, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.30/1.37  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.30/1.37  tff(f_47, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.30/1.37  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.30/1.37  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.30/1.37  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.30/1.37  tff(f_54, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_mcart_1)).
% 2.30/1.37  tff(c_98, plain, (![A_56, B_57, C_58, D_59]: (k4_tarski(k3_mcart_1(A_56, B_57, C_58), D_59)=k4_mcart_1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.30/1.37  tff(c_24, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.37  tff(c_104, plain, (![A_56, B_57, C_58, D_59]: (k1_mcart_1(k4_mcart_1(A_56, B_57, C_58, D_59))=k3_mcart_1(A_56, B_57, C_58))), inference(superposition, [status(thm), theory('equality')], [c_98, c_24])).
% 2.30/1.37  tff(c_131, plain, (![A_68, B_69, C_70, D_71]: (k4_tarski(k4_tarski(k4_tarski(A_68, B_69), C_70), D_71)=k4_mcart_1(A_68, B_69, C_70, D_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.37  tff(c_143, plain, (![A_68, B_69, C_70, D_71]: (k4_tarski(k4_tarski(A_68, B_69), C_70)=k1_mcart_1(k4_mcart_1(A_68, B_69, C_70, D_71)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_24])).
% 2.30/1.37  tff(c_160, plain, (![A_68, B_69, C_70]: (k4_tarski(k4_tarski(A_68, B_69), C_70)=k3_mcart_1(A_68, B_69, C_70))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_143])).
% 2.30/1.37  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.37  tff(c_209, plain, (![A_81, B_82, C_83]: (k2_zfmisc_1(k1_tarski(A_81), k2_tarski(B_82, C_83))=k2_tarski(k4_tarski(A_81, B_82), k4_tarski(A_81, C_83)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.37  tff(c_225, plain, (![A_81, C_83]: (k2_zfmisc_1(k1_tarski(A_81), k2_tarski(C_83, C_83))=k1_tarski(k4_tarski(A_81, C_83)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_2])).
% 2.30/1.37  tff(c_256, plain, (![A_81, C_83]: (k2_zfmisc_1(k1_tarski(A_81), k1_tarski(C_83))=k1_tarski(k4_tarski(A_81, C_83)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_225])).
% 2.30/1.37  tff(c_265, plain, (![A_84, C_85]: (k2_zfmisc_1(k1_tarski(A_84), k1_tarski(C_85))=k1_tarski(k4_tarski(A_84, C_85)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_225])).
% 2.30/1.37  tff(c_18, plain, (![A_26, B_27, C_28]: (k2_zfmisc_1(k2_zfmisc_1(A_26, B_27), C_28)=k3_zfmisc_1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.37  tff(c_271, plain, (![A_84, C_85, C_28]: (k3_zfmisc_1(k1_tarski(A_84), k1_tarski(C_85), C_28)=k2_zfmisc_1(k1_tarski(k4_tarski(A_84, C_85)), C_28))), inference(superposition, [status(thm), theory('equality')], [c_265, c_18])).
% 2.30/1.37  tff(c_28, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.37  tff(c_400, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_28])).
% 2.30/1.37  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_256, c_400])).
% 2.30/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.37  
% 2.30/1.37  Inference rules
% 2.30/1.37  ----------------------
% 2.30/1.37  #Ref     : 0
% 2.30/1.37  #Sup     : 92
% 2.30/1.37  #Fact    : 0
% 2.30/1.37  #Define  : 0
% 2.30/1.37  #Split   : 0
% 2.30/1.37  #Chain   : 0
% 2.30/1.37  #Close   : 0
% 2.30/1.37  
% 2.30/1.37  Ordering : KBO
% 2.30/1.37  
% 2.30/1.37  Simplification rules
% 2.30/1.37  ----------------------
% 2.30/1.37  #Subsume      : 0
% 2.30/1.37  #Demod        : 44
% 2.30/1.37  #Tautology    : 56
% 2.30/1.37  #SimpNegUnit  : 0
% 2.30/1.37  #BackRed      : 2
% 2.30/1.37  
% 2.30/1.37  #Partial instantiations: 0
% 2.30/1.37  #Strategies tried      : 1
% 2.30/1.37  
% 2.30/1.37  Timing (in seconds)
% 2.30/1.37  ----------------------
% 2.30/1.37  Preprocessing        : 0.34
% 2.30/1.37  Parsing              : 0.19
% 2.30/1.37  CNF conversion       : 0.02
% 2.30/1.37  Main loop            : 0.23
% 2.30/1.37  Inferencing          : 0.10
% 2.30/1.37  Reduction            : 0.08
% 2.30/1.37  Demodulation         : 0.06
% 2.30/1.37  BG Simplification    : 0.02
% 2.30/1.37  Subsumption          : 0.02
% 2.30/1.37  Abstraction          : 0.02
% 2.30/1.37  MUC search           : 0.00
% 2.30/1.37  Cooper               : 0.00
% 2.30/1.37  Total                : 0.59
% 2.30/1.37  Index Insertion      : 0.00
% 2.30/1.37  Index Deletion       : 0.00
% 2.30/1.37  Index Matching       : 0.00
% 2.30/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
