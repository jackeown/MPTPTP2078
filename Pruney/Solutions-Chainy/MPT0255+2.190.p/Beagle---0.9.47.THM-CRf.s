%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_xboole_0(A_14,B_15),C_16) = k2_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_xboole_0(k1_tarski(B_19),C_20)) = k2_xboole_0(k2_tarski(A_18,B_19),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_tarski(A_18,B_19),C_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_6])).

tff(c_8,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.23  
% 1.73/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.23  %$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.73/1.23  
% 1.73/1.23  %Foreground sorts:
% 1.73/1.23  
% 1.73/1.23  
% 1.73/1.23  %Background operators:
% 1.73/1.23  
% 1.73/1.23  
% 1.73/1.23  %Foreground operators:
% 1.73/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.23  
% 1.73/1.24  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.73/1.24  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.73/1.24  tff(f_32, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.73/1.24  tff(f_36, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.73/1.24  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.24  tff(c_26, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_xboole_0(A_14, B_15), C_16)=k2_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.24  tff(c_62, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_xboole_0(k1_tarski(B_19), C_20))=k2_xboole_0(k2_tarski(A_18, B_19), C_20))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26])).
% 1.73/1.24  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.24  tff(c_73, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_tarski(A_18, B_19), C_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_6])).
% 1.73/1.24  tff(c_8, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.24  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_8])).
% 1.73/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.24  
% 1.73/1.24  Inference rules
% 1.73/1.24  ----------------------
% 1.73/1.24  #Ref     : 0
% 1.73/1.24  #Sup     : 21
% 1.73/1.24  #Fact    : 0
% 1.73/1.24  #Define  : 0
% 1.73/1.24  #Split   : 0
% 1.73/1.24  #Chain   : 0
% 1.73/1.24  #Close   : 0
% 1.73/1.24  
% 1.73/1.24  Ordering : KBO
% 1.73/1.24  
% 1.73/1.24  Simplification rules
% 1.73/1.24  ----------------------
% 1.73/1.24  #Subsume      : 0
% 1.73/1.24  #Demod        : 12
% 1.73/1.24  #Tautology    : 14
% 1.73/1.24  #SimpNegUnit  : 1
% 1.73/1.24  #BackRed      : 1
% 1.73/1.24  
% 1.73/1.24  #Partial instantiations: 0
% 1.73/1.24  #Strategies tried      : 1
% 1.73/1.24  
% 1.73/1.24  Timing (in seconds)
% 1.73/1.24  ----------------------
% 1.78/1.25  Preprocessing        : 0.32
% 1.78/1.25  Parsing              : 0.17
% 1.78/1.25  CNF conversion       : 0.02
% 1.78/1.25  Main loop            : 0.12
% 1.78/1.25  Inferencing          : 0.05
% 1.78/1.25  Reduction            : 0.04
% 1.78/1.25  Demodulation         : 0.03
% 1.78/1.25  BG Simplification    : 0.01
% 1.78/1.25  Subsumption          : 0.01
% 1.78/1.25  Abstraction          : 0.01
% 1.78/1.25  MUC search           : 0.00
% 1.78/1.25  Cooper               : 0.00
% 1.78/1.25  Total                : 0.46
% 1.78/1.25  Index Insertion      : 0.00
% 1.78/1.25  Index Deletion       : 0.00
% 1.78/1.25  Index Matching       : 0.00
% 1.78/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
