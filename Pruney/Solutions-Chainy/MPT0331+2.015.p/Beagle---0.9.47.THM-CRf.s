%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  49 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(k2_tarski(A_58,C_59),B_60)
      | r2_hidden(C_59,B_60)
      | r2_hidden(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_33,B_34] :
      ( ~ r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_221,plain,(
    ! [A_64,C_65,B_66] :
      ( k3_xboole_0(k2_tarski(A_64,C_65),B_66) = k1_xboole_0
      | r2_hidden(C_65,B_66)
      | r2_hidden(A_64,B_66) ) ),
    inference(resolution,[status(thm)],[c_197,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_236,plain,(
    ! [B_66,A_64,C_65] :
      ( k4_xboole_0(B_66,k2_tarski(A_64,C_65)) = k5_xboole_0(B_66,k1_xboole_0)
      | r2_hidden(C_65,B_66)
      | r2_hidden(A_64,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_88])).

tff(c_325,plain,(
    ! [B_71,A_72,C_73] :
      ( k4_xboole_0(B_71,k2_tarski(A_72,C_73)) = B_71
      | r2_hidden(C_73,B_71)
      | r2_hidden(A_72,B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_236])).

tff(c_22,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_331,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_22])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.34  
% 2.19/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.34  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.19/1.34  
% 2.19/1.34  %Foreground sorts:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Background operators:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Foreground operators:
% 2.19/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.34  
% 2.19/1.35  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.19/1.35  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.19/1.35  tff(f_69, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.19/1.35  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.19/1.35  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.19/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.19/1.35  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/1.35  tff(c_26, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.35  tff(c_24, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.35  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.35  tff(c_197, plain, (![A_58, C_59, B_60]: (r1_xboole_0(k2_tarski(A_58, C_59), B_60) | r2_hidden(C_59, B_60) | r2_hidden(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.35  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.35  tff(c_94, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.35  tff(c_105, plain, (![A_33, B_34]: (~r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_94])).
% 2.19/1.35  tff(c_221, plain, (![A_64, C_65, B_66]: (k3_xboole_0(k2_tarski(A_64, C_65), B_66)=k1_xboole_0 | r2_hidden(C_65, B_66) | r2_hidden(A_64, B_66))), inference(resolution, [status(thm)], [c_197, c_105])).
% 2.19/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.35  tff(c_79, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.35  tff(c_88, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 2.19/1.35  tff(c_236, plain, (![B_66, A_64, C_65]: (k4_xboole_0(B_66, k2_tarski(A_64, C_65))=k5_xboole_0(B_66, k1_xboole_0) | r2_hidden(C_65, B_66) | r2_hidden(A_64, B_66))), inference(superposition, [status(thm), theory('equality')], [c_221, c_88])).
% 2.19/1.35  tff(c_325, plain, (![B_71, A_72, C_73]: (k4_xboole_0(B_71, k2_tarski(A_72, C_73))=B_71 | r2_hidden(C_73, B_71) | r2_hidden(A_72, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_236])).
% 2.19/1.35  tff(c_22, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.35  tff(c_331, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_325, c_22])).
% 2.19/1.35  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_331])).
% 2.19/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.35  
% 2.19/1.35  Inference rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Ref     : 0
% 2.19/1.35  #Sup     : 76
% 2.19/1.35  #Fact    : 0
% 2.19/1.35  #Define  : 0
% 2.19/1.35  #Split   : 1
% 2.19/1.35  #Chain   : 0
% 2.19/1.35  #Close   : 0
% 2.19/1.35  
% 2.19/1.35  Ordering : KBO
% 2.19/1.35  
% 2.19/1.35  Simplification rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Subsume      : 20
% 2.19/1.35  #Demod        : 7
% 2.19/1.35  #Tautology    : 35
% 2.19/1.35  #SimpNegUnit  : 1
% 2.19/1.35  #BackRed      : 0
% 2.19/1.35  
% 2.19/1.35  #Partial instantiations: 0
% 2.19/1.35  #Strategies tried      : 1
% 2.19/1.35  
% 2.19/1.35  Timing (in seconds)
% 2.19/1.35  ----------------------
% 2.19/1.35  Preprocessing        : 0.32
% 2.19/1.35  Parsing              : 0.17
% 2.19/1.36  CNF conversion       : 0.02
% 2.19/1.36  Main loop            : 0.20
% 2.19/1.36  Inferencing          : 0.08
% 2.19/1.36  Reduction            : 0.06
% 2.19/1.36  Demodulation         : 0.05
% 2.19/1.36  BG Simplification    : 0.01
% 2.19/1.36  Subsumption          : 0.03
% 2.19/1.36  Abstraction          : 0.01
% 2.19/1.36  MUC search           : 0.00
% 2.19/1.36  Cooper               : 0.00
% 2.19/1.36  Total                : 0.54
% 2.19/1.36  Index Insertion      : 0.00
% 2.19/1.36  Index Deletion       : 0.00
% 2.19/1.36  Index Matching       : 0.00
% 2.19/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
