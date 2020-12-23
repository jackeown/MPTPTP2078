%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:38 EST 2020

% Result     : Theorem 20.30s
% Output     : CNFRefutation 20.36s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D),k3_mcart_1(A,B,E),k3_mcart_1(A,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_zfmisc_1(k1_tarski(A_18),k2_tarski(B_19,C_20),k1_tarski(D_21)) = k2_tarski(k3_mcart_1(A_18,B_19,D_21),k3_mcart_1(A_18,C_20,D_21)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [C_47,A_48,B_49] : k2_xboole_0(k2_zfmisc_1(C_47,k1_tarski(A_48)),k2_zfmisc_1(C_47,k1_tarski(B_49))) = k2_zfmisc_1(C_47,k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [A_15,B_16,A_48,B_49] : k2_xboole_0(k3_zfmisc_1(A_15,B_16,k1_tarski(A_48)),k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),k1_tarski(B_49))) = k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_408,plain,(
    ! [A_68,B_69,A_70,B_71] : k2_xboole_0(k3_zfmisc_1(A_68,B_69,k1_tarski(A_70)),k3_zfmisc_1(A_68,B_69,k1_tarski(B_71))) = k3_zfmisc_1(A_68,B_69,k2_tarski(A_70,B_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_130])).

tff(c_6241,plain,(
    ! [B_251,B_249,C_248,D_250,A_247] : k2_xboole_0(k2_tarski(k3_mcart_1(A_247,B_251,D_250),k3_mcart_1(A_247,C_248,D_250)),k3_zfmisc_1(k1_tarski(A_247),k2_tarski(B_251,C_248),k1_tarski(B_249))) = k3_zfmisc_1(k1_tarski(A_247),k2_tarski(B_251,C_248),k2_tarski(D_250,B_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_408])).

tff(c_197,plain,(
    ! [A_55,B_56,C_57,D_58] : k3_zfmisc_1(k1_tarski(A_55),k2_tarski(B_56,C_57),k1_tarski(D_58)) = k2_tarski(k3_mcart_1(A_55,B_56,D_58),k3_mcart_1(A_55,C_57,D_58)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_220,plain,(
    ! [B_56,B_2,A_1,C_57,A_55,D_58] : k2_xboole_0(k2_tarski(A_1,B_2),k3_zfmisc_1(k1_tarski(A_55),k2_tarski(B_56,C_57),k1_tarski(D_58))) = k2_enumset1(A_1,B_2,k3_mcart_1(A_55,B_56,D_58),k3_mcart_1(A_55,C_57,D_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_2])).

tff(c_6247,plain,(
    ! [B_251,B_249,C_248,D_250,A_247] : k2_enumset1(k3_mcart_1(A_247,B_251,D_250),k3_mcart_1(A_247,C_248,D_250),k3_mcart_1(A_247,B_251,B_249),k3_mcart_1(A_247,C_248,B_249)) = k3_zfmisc_1(k1_tarski(A_247),k2_tarski(B_251,C_248),k2_tarski(D_250,B_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6241,c_220])).

tff(c_18,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_2','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_2','#skF_5'),k3_mcart_1('#skF_1','#skF_3','#skF_5')) != k3_zfmisc_1(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6247,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.30/10.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.30/10.92  
% 20.30/10.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.36/10.92  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.36/10.92  
% 20.36/10.92  %Foreground sorts:
% 20.36/10.92  
% 20.36/10.92  
% 20.36/10.92  %Background operators:
% 20.36/10.92  
% 20.36/10.92  
% 20.36/10.92  %Foreground operators:
% 20.36/10.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.36/10.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.36/10.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.36/10.92  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 20.36/10.92  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 20.36/10.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.36/10.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.36/10.92  tff('#skF_5', type, '#skF_5': $i).
% 20.36/10.92  tff('#skF_2', type, '#skF_2': $i).
% 20.36/10.92  tff('#skF_3', type, '#skF_3': $i).
% 20.36/10.92  tff('#skF_1', type, '#skF_1': $i).
% 20.36/10.92  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 20.36/10.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.36/10.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.36/10.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.36/10.92  tff('#skF_4', type, '#skF_4': $i).
% 20.36/10.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.36/10.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.36/10.92  
% 20.36/10.93  tff(f_41, axiom, (![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_mcart_1)).
% 20.36/10.93  tff(f_39, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 20.36/10.93  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 20.36/10.93  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 20.36/10.93  tff(f_44, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D), k3_mcart_1(A, B, E), k3_mcart_1(A, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_mcart_1)).
% 20.36/10.93  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (k3_zfmisc_1(k1_tarski(A_18), k2_tarski(B_19, C_20), k1_tarski(D_21))=k2_tarski(k3_mcart_1(A_18, B_19, D_21), k3_mcart_1(A_18, C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.36/10.93  tff(c_14, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.36/10.93  tff(c_120, plain, (![C_47, A_48, B_49]: (k2_xboole_0(k2_zfmisc_1(C_47, k1_tarski(A_48)), k2_zfmisc_1(C_47, k1_tarski(B_49)))=k2_zfmisc_1(C_47, k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.36/10.93  tff(c_130, plain, (![A_15, B_16, A_48, B_49]: (k2_xboole_0(k3_zfmisc_1(A_15, B_16, k1_tarski(A_48)), k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), k1_tarski(B_49)))=k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_120])).
% 20.36/10.93  tff(c_408, plain, (![A_68, B_69, A_70, B_71]: (k2_xboole_0(k3_zfmisc_1(A_68, B_69, k1_tarski(A_70)), k3_zfmisc_1(A_68, B_69, k1_tarski(B_71)))=k3_zfmisc_1(A_68, B_69, k2_tarski(A_70, B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_130])).
% 20.36/10.93  tff(c_6241, plain, (![B_251, B_249, C_248, D_250, A_247]: (k2_xboole_0(k2_tarski(k3_mcart_1(A_247, B_251, D_250), k3_mcart_1(A_247, C_248, D_250)), k3_zfmisc_1(k1_tarski(A_247), k2_tarski(B_251, C_248), k1_tarski(B_249)))=k3_zfmisc_1(k1_tarski(A_247), k2_tarski(B_251, C_248), k2_tarski(D_250, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_408])).
% 20.36/10.93  tff(c_197, plain, (![A_55, B_56, C_57, D_58]: (k3_zfmisc_1(k1_tarski(A_55), k2_tarski(B_56, C_57), k1_tarski(D_58))=k2_tarski(k3_mcart_1(A_55, B_56, D_58), k3_mcart_1(A_55, C_57, D_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.36/10.93  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.36/10.93  tff(c_220, plain, (![B_56, B_2, A_1, C_57, A_55, D_58]: (k2_xboole_0(k2_tarski(A_1, B_2), k3_zfmisc_1(k1_tarski(A_55), k2_tarski(B_56, C_57), k1_tarski(D_58)))=k2_enumset1(A_1, B_2, k3_mcart_1(A_55, B_56, D_58), k3_mcart_1(A_55, C_57, D_58)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_2])).
% 20.36/10.93  tff(c_6247, plain, (![B_251, B_249, C_248, D_250, A_247]: (k2_enumset1(k3_mcart_1(A_247, B_251, D_250), k3_mcart_1(A_247, C_248, D_250), k3_mcart_1(A_247, B_251, B_249), k3_mcart_1(A_247, C_248, B_249))=k3_zfmisc_1(k1_tarski(A_247), k2_tarski(B_251, C_248), k2_tarski(D_250, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_6241, c_220])).
% 20.36/10.93  tff(c_18, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_2', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_2', '#skF_5'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 20.36/10.93  tff(c_27029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6247, c_18])).
% 20.36/10.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.36/10.93  
% 20.36/10.93  Inference rules
% 20.36/10.93  ----------------------
% 20.36/10.93  #Ref     : 0
% 20.36/10.93  #Sup     : 6901
% 20.36/10.93  #Fact    : 0
% 20.36/10.93  #Define  : 0
% 20.36/10.93  #Split   : 0
% 20.36/10.93  #Chain   : 0
% 20.36/10.93  #Close   : 0
% 20.36/10.93  
% 20.36/10.93  Ordering : KBO
% 20.36/10.93  
% 20.36/10.93  Simplification rules
% 20.36/10.93  ----------------------
% 20.36/10.93  #Subsume      : 1138
% 20.36/10.93  #Demod        : 3831
% 20.36/10.93  #Tautology    : 960
% 20.36/10.93  #SimpNegUnit  : 0
% 20.36/10.93  #BackRed      : 1
% 20.36/10.93  
% 20.36/10.93  #Partial instantiations: 0
% 20.36/10.93  #Strategies tried      : 1
% 20.36/10.93  
% 20.36/10.93  Timing (in seconds)
% 20.36/10.93  ----------------------
% 20.36/10.94  Preprocessing        : 0.26
% 20.36/10.94  Parsing              : 0.14
% 20.36/10.94  CNF conversion       : 0.02
% 20.36/10.94  Main loop            : 9.84
% 20.36/10.94  Inferencing          : 2.42
% 20.36/10.94  Reduction            : 5.83
% 20.36/10.94  Demodulation         : 5.45
% 20.36/10.94  BG Simplification    : 0.45
% 20.36/10.94  Subsumption          : 0.91
% 20.36/10.94  Abstraction          : 0.71
% 20.36/10.94  MUC search           : 0.00
% 20.36/10.94  Cooper               : 0.00
% 20.36/10.94  Total                : 10.13
% 20.36/10.94  Index Insertion      : 0.00
% 20.36/10.94  Index Deletion       : 0.00
% 20.36/10.94  Index Matching       : 0.00
% 20.36/10.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
