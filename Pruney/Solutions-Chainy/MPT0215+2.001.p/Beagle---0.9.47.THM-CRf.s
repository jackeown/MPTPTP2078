%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:39 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [A_45,B_46] : k2_enumset1(A_45,A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_27] : k2_enumset1(A_27,A_27,A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_184,plain,(
    ! [B_46] : k2_tarski(B_46,B_46) = k1_tarski(B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_22])).

tff(c_386,plain,(
    ! [B_67,A_68,C_69] : k2_xboole_0(k2_tarski(B_67,A_68),k2_tarski(C_69,A_68)) = k1_enumset1(A_68,B_67,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_631,plain,(
    ! [B_79,A_80,C_81] : r1_tarski(k2_tarski(B_79,A_80),k1_enumset1(A_80,B_79,C_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_8])).

tff(c_637,plain,(
    ! [B_46,C_81] : r1_tarski(k1_tarski(B_46),k1_enumset1(B_46,B_46,C_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_631])).

tff(c_656,plain,(
    ! [B_82,C_83] : r1_tarski(k1_tarski(B_82),k2_tarski(B_82,C_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_637])).

tff(c_671,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_656])).

tff(c_24,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_679,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_671,c_24])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.31  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.33/1.31  
% 2.33/1.31  %Foreground sorts:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Background operators:
% 2.33/1.31  
% 2.33/1.31  
% 2.33/1.31  %Foreground operators:
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.31  
% 2.33/1.32  tff(f_58, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.33/1.32  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.32  tff(f_47, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.33/1.32  tff(f_49, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 2.33/1.32  tff(f_41, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 2.33/1.32  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.33/1.32  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.33/1.32  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.32  tff(c_28, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.32  tff(c_18, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.32  tff(c_177, plain, (![A_45, B_46]: (k2_enumset1(A_45, A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.32  tff(c_22, plain, (![A_27]: (k2_enumset1(A_27, A_27, A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.32  tff(c_184, plain, (![B_46]: (k2_tarski(B_46, B_46)=k1_tarski(B_46))), inference(superposition, [status(thm), theory('equality')], [c_177, c_22])).
% 2.33/1.32  tff(c_386, plain, (![B_67, A_68, C_69]: (k2_xboole_0(k2_tarski(B_67, A_68), k2_tarski(C_69, A_68))=k1_enumset1(A_68, B_67, C_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.32  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.32  tff(c_631, plain, (![B_79, A_80, C_81]: (r1_tarski(k2_tarski(B_79, A_80), k1_enumset1(A_80, B_79, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_386, c_8])).
% 2.33/1.32  tff(c_637, plain, (![B_46, C_81]: (r1_tarski(k1_tarski(B_46), k1_enumset1(B_46, B_46, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_631])).
% 2.33/1.32  tff(c_656, plain, (![B_82, C_83]: (r1_tarski(k1_tarski(B_82), k2_tarski(B_82, C_83)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_637])).
% 2.33/1.32  tff(c_671, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_656])).
% 2.33/1.32  tff(c_24, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.32  tff(c_679, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_671, c_24])).
% 2.33/1.32  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_679])).
% 2.33/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  Inference rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Ref     : 0
% 2.33/1.32  #Sup     : 167
% 2.33/1.32  #Fact    : 0
% 2.33/1.32  #Define  : 0
% 2.33/1.32  #Split   : 0
% 2.33/1.32  #Chain   : 0
% 2.33/1.32  #Close   : 0
% 2.33/1.32  
% 2.33/1.32  Ordering : KBO
% 2.33/1.32  
% 2.33/1.32  Simplification rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Subsume      : 6
% 2.33/1.32  #Demod        : 45
% 2.33/1.32  #Tautology    : 82
% 2.33/1.32  #SimpNegUnit  : 1
% 2.33/1.32  #BackRed      : 0
% 2.33/1.32  
% 2.33/1.32  #Partial instantiations: 0
% 2.33/1.32  #Strategies tried      : 1
% 2.33/1.32  
% 2.33/1.32  Timing (in seconds)
% 2.33/1.32  ----------------------
% 2.33/1.32  Preprocessing        : 0.29
% 2.33/1.32  Parsing              : 0.16
% 2.33/1.32  CNF conversion       : 0.02
% 2.33/1.32  Main loop            : 0.28
% 2.33/1.32  Inferencing          : 0.10
% 2.33/1.32  Reduction            : 0.11
% 2.33/1.32  Demodulation         : 0.09
% 2.33/1.32  BG Simplification    : 0.02
% 2.33/1.32  Subsumption          : 0.05
% 2.33/1.32  Abstraction          : 0.01
% 2.33/1.32  MUC search           : 0.00
% 2.33/1.32  Cooper               : 0.00
% 2.33/1.32  Total                : 0.60
% 2.33/1.32  Index Insertion      : 0.00
% 2.33/1.32  Index Deletion       : 0.00
% 2.33/1.32  Index Matching       : 0.00
% 2.33/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
