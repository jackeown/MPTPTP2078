%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  22 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_166,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k1_tarski(A_35),k2_tarski(B_36,C_37)) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_612,plain,(
    ! [B_66,C_67,A_68] : k2_xboole_0(k2_tarski(B_66,C_67),k1_tarski(A_68)) = k1_enumset1(A_68,B_66,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_618,plain,(
    ! [B_66,C_67,A_68] : k1_enumset1(B_66,C_67,A_68) = k1_enumset1(A_68,B_66,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_6])).

tff(c_16,plain,(
    ! [A_19,C_21,B_20] : k1_enumset1(A_19,C_21,B_20) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_618,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:16:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.21/1.26  
% 2.21/1.26  %Foreground sorts:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Background operators:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Foreground operators:
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.26  
% 2.21/1.27  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.21/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.21/1.27  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.21/1.27  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.21/1.27  tff(f_44, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.21/1.27  tff(c_166, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(B_36, C_37))=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.27  tff(c_612, plain, (![B_66, C_67, A_68]: (k2_xboole_0(k2_tarski(B_66, C_67), k1_tarski(A_68))=k1_enumset1(A_68, B_66, C_67))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 2.21/1.27  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.27  tff(c_618, plain, (![B_66, C_67, A_68]: (k1_enumset1(B_66, C_67, A_68)=k1_enumset1(A_68, B_66, C_67))), inference(superposition, [status(thm), theory('equality')], [c_612, c_6])).
% 2.21/1.27  tff(c_16, plain, (![A_19, C_21, B_20]: (k1_enumset1(A_19, C_21, B_20)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.27  tff(c_18, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.27  tff(c_19, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.21/1.27  tff(c_655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_618, c_618, c_19])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 152
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 0
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.27  Ordering : KBO
% 2.21/1.27  
% 2.21/1.27  Simplification rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Subsume      : 8
% 2.21/1.27  #Demod        : 92
% 2.21/1.27  #Tautology    : 110
% 2.21/1.27  #SimpNegUnit  : 0
% 2.21/1.27  #BackRed      : 2
% 2.21/1.27  
% 2.21/1.27  #Partial instantiations: 0
% 2.21/1.27  #Strategies tried      : 1
% 2.21/1.27  
% 2.21/1.27  Timing (in seconds)
% 2.21/1.27  ----------------------
% 2.21/1.27  Preprocessing        : 0.26
% 2.21/1.27  Parsing              : 0.14
% 2.21/1.27  CNF conversion       : 0.01
% 2.21/1.27  Main loop            : 0.26
% 2.21/1.27  Inferencing          : 0.09
% 2.21/1.27  Reduction            : 0.10
% 2.21/1.27  Demodulation         : 0.09
% 2.21/1.27  BG Simplification    : 0.01
% 2.21/1.27  Subsumption          : 0.04
% 2.21/1.27  Abstraction          : 0.01
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.54
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
