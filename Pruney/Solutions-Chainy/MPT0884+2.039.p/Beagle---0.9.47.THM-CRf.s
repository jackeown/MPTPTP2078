%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:36 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_14,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_zfmisc_1(k2_tarski(A_14,B_15),k1_tarski(C_16),k1_tarski(D_17)) = k2_tarski(k3_mcart_1(A_14,C_16,D_17),k3_mcart_1(B_15,C_16,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [C_43,A_44,B_45] : k2_xboole_0(k2_zfmisc_1(C_43,k1_tarski(A_44)),k2_zfmisc_1(C_43,k1_tarski(B_45))) = k2_zfmisc_1(C_43,k2_tarski(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_195,plain,(
    ! [A_11,B_12,A_44,B_45] : k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),k1_tarski(A_44)),k3_zfmisc_1(A_11,B_12,k1_tarski(B_45))) = k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_173])).

tff(c_262,plain,(
    ! [A_53,B_54,A_55,B_56] : k2_xboole_0(k3_zfmisc_1(A_53,B_54,k1_tarski(A_55)),k3_zfmisc_1(A_53,B_54,k1_tarski(B_56))) = k3_zfmisc_1(A_53,B_54,k2_tarski(A_55,B_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_195])).

tff(c_799,plain,(
    ! [D_99,B_102,C_101,A_100,A_103] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_103,B_102),k1_tarski(C_101),k1_tarski(A_100)),k2_tarski(k3_mcart_1(A_103,C_101,D_99),k3_mcart_1(B_102,C_101,D_99))) = k3_zfmisc_1(k2_tarski(A_103,B_102),k1_tarski(C_101),k2_tarski(A_100,D_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_262])).

tff(c_202,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_zfmisc_1(k2_tarski(A_46,B_47),k1_tarski(C_48),k1_tarski(D_49)) = k2_tarski(k3_mcart_1(A_46,C_48,D_49),k3_mcart_1(B_47,C_48,D_49)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_220,plain,(
    ! [A_46,B_47,C_3,D_4,C_48,D_49] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_46,B_47),k1_tarski(C_48),k1_tarski(D_49)),k2_tarski(C_3,D_4)) = k2_enumset1(k3_mcart_1(A_46,C_48,D_49),k3_mcart_1(B_47,C_48,D_49),C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2])).

tff(c_805,plain,(
    ! [D_99,B_102,C_101,A_100,A_103] : k2_enumset1(k3_mcart_1(A_103,C_101,A_100),k3_mcart_1(B_102,C_101,A_100),k3_mcart_1(A_103,C_101,D_99),k3_mcart_1(B_102,C_101,D_99)) = k3_zfmisc_1(k2_tarski(A_103,B_102),k1_tarski(C_101),k2_tarski(A_100,D_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_220])).

tff(c_16,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:48:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.11/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.53  
% 3.25/1.54  tff(f_39, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_mcart_1)).
% 3.25/1.54  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.25/1.54  tff(f_35, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 3.25/1.54  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.25/1.54  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 3.25/1.54  tff(c_14, plain, (![A_14, B_15, C_16, D_17]: (k3_zfmisc_1(k2_tarski(A_14, B_15), k1_tarski(C_16), k1_tarski(D_17))=k2_tarski(k3_mcart_1(A_14, C_16, D_17), k3_mcart_1(B_15, C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.54  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.54  tff(c_173, plain, (![C_43, A_44, B_45]: (k2_xboole_0(k2_zfmisc_1(C_43, k1_tarski(A_44)), k2_zfmisc_1(C_43, k1_tarski(B_45)))=k2_zfmisc_1(C_43, k2_tarski(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.54  tff(c_195, plain, (![A_11, B_12, A_44, B_45]: (k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), k1_tarski(A_44)), k3_zfmisc_1(A_11, B_12, k1_tarski(B_45)))=k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_173])).
% 3.25/1.54  tff(c_262, plain, (![A_53, B_54, A_55, B_56]: (k2_xboole_0(k3_zfmisc_1(A_53, B_54, k1_tarski(A_55)), k3_zfmisc_1(A_53, B_54, k1_tarski(B_56)))=k3_zfmisc_1(A_53, B_54, k2_tarski(A_55, B_56)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_195])).
% 3.25/1.54  tff(c_799, plain, (![D_99, B_102, C_101, A_100, A_103]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_103, B_102), k1_tarski(C_101), k1_tarski(A_100)), k2_tarski(k3_mcart_1(A_103, C_101, D_99), k3_mcart_1(B_102, C_101, D_99)))=k3_zfmisc_1(k2_tarski(A_103, B_102), k1_tarski(C_101), k2_tarski(A_100, D_99)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_262])).
% 3.25/1.54  tff(c_202, plain, (![A_46, B_47, C_48, D_49]: (k3_zfmisc_1(k2_tarski(A_46, B_47), k1_tarski(C_48), k1_tarski(D_49))=k2_tarski(k3_mcart_1(A_46, C_48, D_49), k3_mcart_1(B_47, C_48, D_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.54  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.54  tff(c_220, plain, (![A_46, B_47, C_3, D_4, C_48, D_49]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_46, B_47), k1_tarski(C_48), k1_tarski(D_49)), k2_tarski(C_3, D_4))=k2_enumset1(k3_mcart_1(A_46, C_48, D_49), k3_mcart_1(B_47, C_48, D_49), C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_202, c_2])).
% 3.25/1.54  tff(c_805, plain, (![D_99, B_102, C_101, A_100, A_103]: (k2_enumset1(k3_mcart_1(A_103, C_101, A_100), k3_mcart_1(B_102, C_101, A_100), k3_mcart_1(A_103, C_101, D_99), k3_mcart_1(B_102, C_101, D_99))=k3_zfmisc_1(k2_tarski(A_103, B_102), k1_tarski(C_101), k2_tarski(A_100, D_99)))), inference(superposition, [status(thm), theory('equality')], [c_799, c_220])).
% 3.25/1.54  tff(c_16, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.25/1.54  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_805, c_16])).
% 3.25/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.54  
% 3.25/1.54  Inference rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Ref     : 0
% 3.25/1.54  #Sup     : 203
% 3.25/1.54  #Fact    : 0
% 3.25/1.54  #Define  : 0
% 3.25/1.54  #Split   : 0
% 3.25/1.54  #Chain   : 0
% 3.25/1.54  #Close   : 0
% 3.25/1.54  
% 3.25/1.54  Ordering : KBO
% 3.25/1.54  
% 3.25/1.54  Simplification rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Subsume      : 24
% 3.25/1.54  #Demod        : 131
% 3.25/1.54  #Tautology    : 120
% 3.25/1.54  #SimpNegUnit  : 0
% 3.25/1.54  #BackRed      : 1
% 3.25/1.54  
% 3.25/1.54  #Partial instantiations: 0
% 3.25/1.54  #Strategies tried      : 1
% 3.25/1.54  
% 3.25/1.54  Timing (in seconds)
% 3.25/1.54  ----------------------
% 3.25/1.54  Preprocessing        : 0.31
% 3.25/1.54  Parsing              : 0.16
% 3.25/1.54  CNF conversion       : 0.02
% 3.25/1.54  Main loop            : 0.43
% 3.25/1.54  Inferencing          : 0.19
% 3.25/1.54  Reduction            : 0.16
% 3.25/1.54  Demodulation         : 0.13
% 3.25/1.54  BG Simplification    : 0.02
% 3.25/1.54  Subsumption          : 0.04
% 3.25/1.54  Abstraction          : 0.04
% 3.25/1.54  MUC search           : 0.00
% 3.25/1.54  Cooper               : 0.00
% 3.25/1.54  Total                : 0.76
% 3.25/1.54  Index Insertion      : 0.00
% 3.25/1.54  Index Deletion       : 0.00
% 3.25/1.54  Index Matching       : 0.00
% 3.25/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
