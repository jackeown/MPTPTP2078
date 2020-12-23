%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  45 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_tarski(A_25),B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(k1_tarski(A_56),B_57) = k1_xboole_0
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_173,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_34])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_49,B_50] :
      ( ~ r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_265,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(k1_tarski(A_77),B_78) = k1_xboole_0
      | r2_hidden(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_30,c_130])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_280,plain,(
    ! [A_77,B_78] :
      ( k5_xboole_0(k1_tarski(A_77),k1_xboole_0) = k4_xboole_0(k1_tarski(A_77),B_78)
      | r2_hidden(A_77,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_14])).

tff(c_397,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k1_tarski(A_85),B_86) = k1_tarski(A_85)
      | r2_hidden(A_85,B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_280])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_413,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_32])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:37:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.34  
% 2.20/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.20/1.35  
% 2.20/1.35  %Foreground sorts:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Background operators:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Foreground operators:
% 2.20/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.35  
% 2.20/1.36  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.20/1.36  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.20/1.36  tff(f_79, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.20/1.36  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.20/1.36  tff(f_74, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.20/1.36  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.20/1.36  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.20/1.36  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.20/1.36  tff(c_28, plain, (![A_25, B_26]: (r1_tarski(k1_tarski(A_25), B_26) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.36  tff(c_100, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.36  tff(c_159, plain, (![A_56, B_57]: (k4_xboole_0(k1_tarski(A_56), B_57)=k1_xboole_0 | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.20/1.36  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.36  tff(c_173, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_159, c_34])).
% 2.20/1.36  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.36  tff(c_30, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.20/1.36  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.36  tff(c_118, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.36  tff(c_130, plain, (![A_49, B_50]: (~r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_118])).
% 2.20/1.36  tff(c_265, plain, (![A_77, B_78]: (k3_xboole_0(k1_tarski(A_77), B_78)=k1_xboole_0 | r2_hidden(A_77, B_78))), inference(resolution, [status(thm)], [c_30, c_130])).
% 2.20/1.36  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.36  tff(c_280, plain, (![A_77, B_78]: (k5_xboole_0(k1_tarski(A_77), k1_xboole_0)=k4_xboole_0(k1_tarski(A_77), B_78) | r2_hidden(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_265, c_14])).
% 2.20/1.36  tff(c_397, plain, (![A_85, B_86]: (k4_xboole_0(k1_tarski(A_85), B_86)=k1_tarski(A_85) | r2_hidden(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_280])).
% 2.20/1.36  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.36  tff(c_413, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_397, c_32])).
% 2.20/1.36  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_413])).
% 2.20/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.36  
% 2.20/1.36  Inference rules
% 2.20/1.36  ----------------------
% 2.20/1.36  #Ref     : 0
% 2.20/1.36  #Sup     : 97
% 2.20/1.36  #Fact    : 0
% 2.20/1.36  #Define  : 0
% 2.20/1.36  #Split   : 0
% 2.20/1.36  #Chain   : 0
% 2.20/1.36  #Close   : 0
% 2.20/1.36  
% 2.20/1.36  Ordering : KBO
% 2.20/1.36  
% 2.20/1.36  Simplification rules
% 2.20/1.36  ----------------------
% 2.20/1.36  #Subsume      : 24
% 2.20/1.36  #Demod        : 7
% 2.20/1.36  #Tautology    : 45
% 2.20/1.36  #SimpNegUnit  : 1
% 2.20/1.36  #BackRed      : 0
% 2.20/1.36  
% 2.20/1.36  #Partial instantiations: 0
% 2.20/1.36  #Strategies tried      : 1
% 2.20/1.36  
% 2.20/1.36  Timing (in seconds)
% 2.20/1.36  ----------------------
% 2.20/1.36  Preprocessing        : 0.32
% 2.20/1.36  Parsing              : 0.18
% 2.20/1.36  CNF conversion       : 0.02
% 2.20/1.36  Main loop            : 0.20
% 2.20/1.36  Inferencing          : 0.09
% 2.20/1.36  Reduction            : 0.06
% 2.20/1.36  Demodulation         : 0.04
% 2.20/1.36  BG Simplification    : 0.01
% 2.20/1.36  Subsumption          : 0.03
% 2.20/1.36  Abstraction          : 0.01
% 2.20/1.36  MUC search           : 0.00
% 2.20/1.36  Cooper               : 0.00
% 2.20/1.36  Total                : 0.55
% 2.20/1.36  Index Insertion      : 0.00
% 2.20/1.36  Index Deletion       : 0.00
% 2.20/1.36  Index Matching       : 0.00
% 2.20/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
