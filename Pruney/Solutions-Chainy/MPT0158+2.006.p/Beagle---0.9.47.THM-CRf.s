%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k1_enumset1(D_6,E_7,F_8)) = k4_enumset1(A_3,B_4,C_5,D_6,E_7,F_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [E_72,C_70,A_74,F_68,G_73,B_69,D_71] : k2_xboole_0(k2_enumset1(A_74,B_69,C_70,D_71),k1_enumset1(E_72,F_68,G_73)) = k5_enumset1(A_74,B_69,C_70,D_71,E_72,F_68,G_73) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [E_72,F_68,A_25,G_73,C_27,B_26] : k5_enumset1(A_25,A_25,B_26,C_27,E_72,F_68,G_73) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k1_enumset1(E_72,F_68,G_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_117])).

tff(c_132,plain,(
    ! [E_72,F_68,A_25,G_73,C_27,B_26] : k5_enumset1(A_25,A_25,B_26,C_27,E_72,F_68,G_73) = k4_enumset1(A_25,B_26,C_27,E_72,F_68,G_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_18,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.16  
% 1.92/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.16  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.16  
% 1.92/1.16  %Foreground sorts:
% 1.92/1.16  
% 1.92/1.16  
% 1.92/1.16  %Background operators:
% 1.92/1.16  
% 1.92/1.16  
% 1.92/1.16  %Foreground operators:
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.16  
% 1.92/1.17  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 1.92/1.17  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.92/1.17  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 1.92/1.17  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.92/1.17  tff(c_4, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k1_enumset1(D_6, E_7, F_8))=k4_enumset1(A_3, B_4, C_5, D_6, E_7, F_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.17  tff(c_12, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.17  tff(c_117, plain, (![E_72, C_70, A_74, F_68, G_73, B_69, D_71]: (k2_xboole_0(k2_enumset1(A_74, B_69, C_70, D_71), k1_enumset1(E_72, F_68, G_73))=k5_enumset1(A_74, B_69, C_70, D_71, E_72, F_68, G_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.17  tff(c_126, plain, (![E_72, F_68, A_25, G_73, C_27, B_26]: (k5_enumset1(A_25, A_25, B_26, C_27, E_72, F_68, G_73)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k1_enumset1(E_72, F_68, G_73)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_117])).
% 1.92/1.17  tff(c_132, plain, (![E_72, F_68, A_25, G_73, C_27, B_26]: (k5_enumset1(A_25, A_25, B_26, C_27, E_72, F_68, G_73)=k4_enumset1(A_25, B_26, C_27, E_72, F_68, G_73))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 1.92/1.17  tff(c_18, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.17  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_18])).
% 1.92/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  Inference rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Ref     : 0
% 1.92/1.17  #Sup     : 34
% 1.92/1.17  #Fact    : 0
% 1.92/1.17  #Define  : 0
% 1.92/1.17  #Split   : 0
% 1.92/1.17  #Chain   : 0
% 1.92/1.17  #Close   : 0
% 1.92/1.17  
% 1.92/1.17  Ordering : KBO
% 1.92/1.17  
% 1.92/1.17  Simplification rules
% 1.92/1.17  ----------------------
% 1.92/1.17  #Subsume      : 1
% 1.92/1.17  #Demod        : 5
% 1.92/1.17  #Tautology    : 26
% 1.92/1.17  #SimpNegUnit  : 0
% 1.92/1.17  #BackRed      : 1
% 1.92/1.17  
% 1.92/1.17  #Partial instantiations: 0
% 1.92/1.17  #Strategies tried      : 1
% 1.92/1.17  
% 1.92/1.17  Timing (in seconds)
% 1.92/1.17  ----------------------
% 1.92/1.17  Preprocessing        : 0.30
% 1.92/1.17  Parsing              : 0.16
% 1.92/1.17  CNF conversion       : 0.02
% 1.92/1.17  Main loop            : 0.13
% 1.92/1.17  Inferencing          : 0.06
% 1.92/1.17  Reduction            : 0.04
% 1.92/1.17  Demodulation         : 0.03
% 1.92/1.17  BG Simplification    : 0.01
% 1.92/1.17  Subsumption          : 0.01
% 1.92/1.17  Abstraction          : 0.01
% 1.92/1.17  MUC search           : 0.00
% 1.92/1.17  Cooper               : 0.00
% 1.92/1.17  Total                : 0.44
% 1.92/1.17  Index Insertion      : 0.00
% 1.92/1.17  Index Deletion       : 0.00
% 1.92/1.17  Index Matching       : 0.00
% 1.92/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
