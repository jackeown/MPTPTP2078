%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:45 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  65 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_730,plain,(
    ! [A_75,B_76,C_77] :
      ( k4_xboole_0(k2_tarski(A_75,B_76),C_77) = k2_tarski(A_75,B_76)
      | r2_hidden(B_76,C_77)
      | r2_hidden(A_75,C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_742,plain,(
    ! [A_75,B_76,C_77] :
      ( k4_xboole_0(k2_tarski(A_75,B_76),k2_tarski(A_75,B_76)) = k3_xboole_0(k2_tarski(A_75,B_76),C_77)
      | r2_hidden(B_76,C_77)
      | r2_hidden(A_75,C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_20])).

tff(c_5895,plain,(
    ! [A_163,B_164,C_165] :
      ( k3_xboole_0(k2_tarski(A_163,B_164),C_165) = k1_xboole_0
      | r2_hidden(B_164,C_165)
      | r2_hidden(A_163,C_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_742])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36967,plain,(
    ! [C_453,A_454,B_455] :
      ( k3_xboole_0(C_453,k2_tarski(A_454,B_455)) = k1_xboole_0
      | r2_hidden(B_455,C_453)
      | r2_hidden(A_454,C_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5895,c_2])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1957,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | k4_xboole_0(A_103,B_102) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_1981,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1957])).

tff(c_2337,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = A_109
      | k3_xboole_0(A_109,B_110) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1981])).

tff(c_34,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2520,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2337,c_34])).

tff(c_37360,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36967,c_2520])).

tff(c_37571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_37360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.49/5.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.11  
% 11.49/5.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.11  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.49/5.11  
% 11.49/5.11  %Foreground sorts:
% 11.49/5.11  
% 11.49/5.11  
% 11.49/5.11  %Background operators:
% 11.49/5.11  
% 11.49/5.11  
% 11.49/5.11  %Foreground operators:
% 11.49/5.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.49/5.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.49/5.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.49/5.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.49/5.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.49/5.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.49/5.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.49/5.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.49/5.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.49/5.11  tff('#skF_2', type, '#skF_2': $i).
% 11.49/5.11  tff('#skF_3', type, '#skF_3': $i).
% 11.49/5.11  tff('#skF_1', type, '#skF_1': $i).
% 11.49/5.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.49/5.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.49/5.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.49/5.11  
% 11.49/5.12  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 11.49/5.12  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.49/5.12  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.49/5.12  tff(f_59, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 11.49/5.12  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.49/5.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.49/5.12  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.49/5.12  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.49/5.12  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.49/5.12  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.49/5.12  tff(c_75, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.49/5.12  tff(c_83, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_75])).
% 11.49/5.12  tff(c_730, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k2_tarski(A_75, B_76), C_77)=k2_tarski(A_75, B_76) | r2_hidden(B_76, C_77) | r2_hidden(A_75, C_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.49/5.12  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.49/5.12  tff(c_742, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k2_tarski(A_75, B_76), k2_tarski(A_75, B_76))=k3_xboole_0(k2_tarski(A_75, B_76), C_77) | r2_hidden(B_76, C_77) | r2_hidden(A_75, C_77))), inference(superposition, [status(thm), theory('equality')], [c_730, c_20])).
% 11.49/5.12  tff(c_5895, plain, (![A_163, B_164, C_165]: (k3_xboole_0(k2_tarski(A_163, B_164), C_165)=k1_xboole_0 | r2_hidden(B_164, C_165) | r2_hidden(A_163, C_165))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_742])).
% 11.49/5.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.49/5.12  tff(c_36967, plain, (![C_453, A_454, B_455]: (k3_xboole_0(C_453, k2_tarski(A_454, B_455))=k1_xboole_0 | r2_hidden(B_455, C_453) | r2_hidden(A_454, C_453))), inference(superposition, [status(thm), theory('equality')], [c_5895, c_2])).
% 11.49/5.12  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.49/5.12  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.49/5.12  tff(c_174, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.49/5.12  tff(c_1957, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | k4_xboole_0(A_103, B_102)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_174])).
% 11.49/5.12  tff(c_1981, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1957])).
% 11.49/5.12  tff(c_2337, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=A_109 | k3_xboole_0(A_109, B_110)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1981])).
% 11.49/5.12  tff(c_34, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.49/5.12  tff(c_2520, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2337, c_34])).
% 11.49/5.12  tff(c_37360, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36967, c_2520])).
% 11.49/5.12  tff(c_37571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_37360])).
% 11.49/5.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/5.12  
% 11.49/5.12  Inference rules
% 11.49/5.12  ----------------------
% 11.49/5.12  #Ref     : 0
% 11.49/5.12  #Sup     : 9237
% 11.49/5.12  #Fact    : 4
% 11.49/5.12  #Define  : 0
% 11.49/5.12  #Split   : 0
% 11.49/5.12  #Chain   : 0
% 11.49/5.12  #Close   : 0
% 11.49/5.12  
% 11.49/5.12  Ordering : KBO
% 11.49/5.12  
% 11.49/5.12  Simplification rules
% 11.49/5.12  ----------------------
% 11.49/5.12  #Subsume      : 450
% 11.49/5.12  #Demod        : 11563
% 11.49/5.12  #Tautology    : 6046
% 11.49/5.12  #SimpNegUnit  : 23
% 11.49/5.12  #BackRed      : 9
% 11.49/5.12  
% 11.49/5.12  #Partial instantiations: 0
% 11.49/5.12  #Strategies tried      : 1
% 11.49/5.12  
% 11.49/5.12  Timing (in seconds)
% 11.49/5.12  ----------------------
% 11.49/5.13  Preprocessing        : 0.29
% 11.49/5.13  Parsing              : 0.15
% 11.49/5.13  CNF conversion       : 0.02
% 11.49/5.13  Main loop            : 4.04
% 11.49/5.13  Inferencing          : 0.72
% 11.49/5.13  Reduction            : 2.44
% 11.49/5.13  Demodulation         : 2.20
% 11.49/5.13  BG Simplification    : 0.08
% 11.49/5.13  Subsumption          : 0.62
% 11.49/5.13  Abstraction          : 0.14
% 11.49/5.13  MUC search           : 0.00
% 11.49/5.13  Cooper               : 0.00
% 11.49/5.13  Total                : 4.35
% 11.49/5.13  Index Insertion      : 0.00
% 11.49/5.13  Index Deletion       : 0.00
% 11.49/5.13  Index Matching       : 0.00
% 11.49/5.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
