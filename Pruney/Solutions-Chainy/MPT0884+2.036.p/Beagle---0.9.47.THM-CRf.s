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
% DateTime   : Thu Dec  3 10:09:36 EST 2020

% Result     : Theorem 25.40s
% Output     : CNFRefutation 25.40s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_213,plain,(
    ! [A_48,B_49,C_50] : k2_zfmisc_1(k2_tarski(A_48,B_49),k1_tarski(C_50)) = k2_tarski(k4_tarski(A_48,C_50),k4_tarski(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_235,plain,(
    ! [A_48,C_50,B_49,C_20] : k2_zfmisc_1(k2_tarski(k4_tarski(A_48,C_50),k4_tarski(B_49,C_50)),C_20) = k3_zfmisc_1(k2_tarski(A_48,B_49),k1_tarski(C_50),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_16])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] : k4_tarski(k4_tarski(A_15,B_16),C_17) = k3_mcart_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_292,plain,(
    ! [A_54,C_55,D_56,B_57] : k2_enumset1(k4_tarski(A_54,C_55),k4_tarski(A_54,D_56),k4_tarski(B_57,C_55),k4_tarski(B_57,D_56)) = k2_zfmisc_1(k2_tarski(A_54,B_57),k2_tarski(C_55,D_56)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_327,plain,(
    ! [B_16,A_15,D_56,C_17,A_54] : k2_enumset1(k4_tarski(A_54,C_17),k4_tarski(A_54,D_56),k3_mcart_1(A_15,B_16,C_17),k4_tarski(k4_tarski(A_15,B_16),D_56)) = k2_zfmisc_1(k2_tarski(A_54,k4_tarski(A_15,B_16)),k2_tarski(C_17,D_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_3852,plain,(
    ! [D_192,A_190,B_191,A_193,C_189] : k2_enumset1(k4_tarski(A_190,C_189),k4_tarski(A_190,D_192),k3_mcart_1(A_193,B_191,C_189),k3_mcart_1(A_193,B_191,D_192)) = k2_zfmisc_1(k2_tarski(A_190,k4_tarski(A_193,B_191)),k2_tarski(C_189,D_192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_3882,plain,(
    ! [B_16,A_15,B_191,A_193,C_189,C_17] : k2_enumset1(k4_tarski(k4_tarski(A_15,B_16),C_189),k3_mcart_1(A_15,B_16,C_17),k3_mcart_1(A_193,B_191,C_189),k3_mcart_1(A_193,B_191,C_17)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_15,B_16),k4_tarski(A_193,B_191)),k2_tarski(C_189,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3852])).

tff(c_3888,plain,(
    ! [B_16,A_15,B_191,A_193,C_189,C_17] : k2_enumset1(k3_mcart_1(A_15,B_16,C_189),k3_mcart_1(A_15,B_16,C_17),k3_mcart_1(A_193,B_191,C_189),k3_mcart_1(A_193,B_191,C_17)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_15,B_16),k4_tarski(A_193,B_191)),k2_tarski(C_189,C_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3882])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] : k2_enumset1(A_1,C_3,B_2,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_39512,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_19])).

tff(c_39515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_39512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.40/15.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.40/15.49  
% 25.40/15.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.40/15.49  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.40/15.49  
% 25.40/15.49  %Foreground sorts:
% 25.40/15.49  
% 25.40/15.49  
% 25.40/15.49  %Background operators:
% 25.40/15.49  
% 25.40/15.49  
% 25.40/15.49  %Foreground operators:
% 25.40/15.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.40/15.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.40/15.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 25.40/15.49  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 25.40/15.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.40/15.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.40/15.49  tff('#skF_5', type, '#skF_5': $i).
% 25.40/15.49  tff('#skF_2', type, '#skF_2': $i).
% 25.40/15.49  tff('#skF_3', type, '#skF_3': $i).
% 25.40/15.49  tff('#skF_1', type, '#skF_1': $i).
% 25.40/15.49  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 25.40/15.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.40/15.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.40/15.49  tff('#skF_4', type, '#skF_4': $i).
% 25.40/15.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.40/15.49  
% 25.40/15.51  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 25.40/15.51  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 25.40/15.51  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 25.40/15.51  tff(f_33, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 25.40/15.51  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 25.40/15.51  tff(f_44, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 25.40/15.51  tff(c_213, plain, (![A_48, B_49, C_50]: (k2_zfmisc_1(k2_tarski(A_48, B_49), k1_tarski(C_50))=k2_tarski(k4_tarski(A_48, C_50), k4_tarski(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.40/15.51  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.40/15.51  tff(c_235, plain, (![A_48, C_50, B_49, C_20]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_48, C_50), k4_tarski(B_49, C_50)), C_20)=k3_zfmisc_1(k2_tarski(A_48, B_49), k1_tarski(C_50), C_20))), inference(superposition, [status(thm), theory('equality')], [c_213, c_16])).
% 25.40/15.51  tff(c_14, plain, (![A_15, B_16, C_17]: (k4_tarski(k4_tarski(A_15, B_16), C_17)=k3_mcart_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.40/15.51  tff(c_292, plain, (![A_54, C_55, D_56, B_57]: (k2_enumset1(k4_tarski(A_54, C_55), k4_tarski(A_54, D_56), k4_tarski(B_57, C_55), k4_tarski(B_57, D_56))=k2_zfmisc_1(k2_tarski(A_54, B_57), k2_tarski(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.40/15.51  tff(c_327, plain, (![B_16, A_15, D_56, C_17, A_54]: (k2_enumset1(k4_tarski(A_54, C_17), k4_tarski(A_54, D_56), k3_mcart_1(A_15, B_16, C_17), k4_tarski(k4_tarski(A_15, B_16), D_56))=k2_zfmisc_1(k2_tarski(A_54, k4_tarski(A_15, B_16)), k2_tarski(C_17, D_56)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_292])).
% 25.40/15.51  tff(c_3852, plain, (![D_192, A_190, B_191, A_193, C_189]: (k2_enumset1(k4_tarski(A_190, C_189), k4_tarski(A_190, D_192), k3_mcart_1(A_193, B_191, C_189), k3_mcart_1(A_193, B_191, D_192))=k2_zfmisc_1(k2_tarski(A_190, k4_tarski(A_193, B_191)), k2_tarski(C_189, D_192)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 25.40/15.51  tff(c_3882, plain, (![B_16, A_15, B_191, A_193, C_189, C_17]: (k2_enumset1(k4_tarski(k4_tarski(A_15, B_16), C_189), k3_mcart_1(A_15, B_16, C_17), k3_mcart_1(A_193, B_191, C_189), k3_mcart_1(A_193, B_191, C_17))=k2_zfmisc_1(k2_tarski(k4_tarski(A_15, B_16), k4_tarski(A_193, B_191)), k2_tarski(C_189, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3852])).
% 25.40/15.51  tff(c_3888, plain, (![B_16, A_15, B_191, A_193, C_189, C_17]: (k2_enumset1(k3_mcart_1(A_15, B_16, C_189), k3_mcart_1(A_15, B_16, C_17), k3_mcart_1(A_193, B_191, C_189), k3_mcart_1(A_193, B_191, C_17))=k2_zfmisc_1(k2_tarski(k4_tarski(A_15, B_16), k4_tarski(A_193, B_191)), k2_tarski(C_189, C_17)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3882])).
% 25.40/15.51  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (k2_enumset1(A_1, C_3, B_2, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.40/15.51  tff(c_18, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 25.40/15.51  tff(c_19, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 25.40/15.51  tff(c_39512, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3888, c_19])).
% 25.40/15.51  tff(c_39515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_39512])).
% 25.40/15.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.40/15.51  
% 25.40/15.51  Inference rules
% 25.40/15.51  ----------------------
% 25.40/15.51  #Ref     : 0
% 25.40/15.51  #Sup     : 9900
% 25.40/15.51  #Fact    : 0
% 25.40/15.51  #Define  : 0
% 25.40/15.51  #Split   : 0
% 25.40/15.51  #Chain   : 0
% 25.40/15.51  #Close   : 0
% 25.40/15.51  
% 25.40/15.51  Ordering : KBO
% 25.40/15.51  
% 25.40/15.51  Simplification rules
% 25.40/15.51  ----------------------
% 25.40/15.51  #Subsume      : 1125
% 25.40/15.51  #Demod        : 17441
% 25.40/15.51  #Tautology    : 2641
% 25.40/15.51  #SimpNegUnit  : 0
% 25.40/15.51  #BackRed      : 1
% 25.40/15.51  
% 25.40/15.51  #Partial instantiations: 0
% 25.40/15.51  #Strategies tried      : 1
% 25.40/15.51  
% 25.40/15.51  Timing (in seconds)
% 25.40/15.51  ----------------------
% 25.40/15.51  Preprocessing        : 0.28
% 25.40/15.51  Parsing              : 0.15
% 25.40/15.51  CNF conversion       : 0.02
% 25.40/15.51  Main loop            : 14.38
% 25.40/15.51  Inferencing          : 3.40
% 25.40/15.51  Reduction            : 8.73
% 25.40/15.51  Demodulation         : 8.09
% 25.40/15.51  BG Simplification    : 0.59
% 25.40/15.51  Subsumption          : 1.38
% 25.40/15.51  Abstraction          : 1.19
% 25.40/15.51  MUC search           : 0.00
% 25.40/15.51  Cooper               : 0.00
% 25.40/15.51  Total                : 14.69
% 25.40/15.51  Index Insertion      : 0.00
% 25.40/15.51  Index Deletion       : 0.00
% 25.40/15.51  Index Matching       : 0.00
% 25.40/15.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
