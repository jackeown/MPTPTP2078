%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_14,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_13] : k1_tarski(A_13) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_139])).

tff(c_165,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_160])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | C_9 = B_8
      | k2_xboole_0(B_8,C_9) != k1_tarski(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,(
    ! [A_7] :
      ( k1_tarski('#skF_2') = k1_xboole_0
      | k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_7) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_10])).

tff(c_222,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_16,c_32,c_219])).

tff(c_227,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  %$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.13  
% 1.71/1.14  tff(f_58, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.71/1.14  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.71/1.14  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.71/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.71/1.14  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.71/1.14  tff(f_45, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.71/1.14  tff(c_14, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.14  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.14  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.14  tff(c_28, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.14  tff(c_32, plain, (![A_13]: (k1_tarski(A_13)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_28])).
% 1.71/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.14  tff(c_18, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.14  tff(c_139, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.14  tff(c_160, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_139])).
% 1.71/1.14  tff(c_165, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_160])).
% 1.71/1.14  tff(c_10, plain, (![C_9, B_8, A_7]: (k1_xboole_0=C_9 | k1_xboole_0=B_8 | C_9=B_8 | k2_xboole_0(B_8, C_9)!=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.14  tff(c_219, plain, (![A_7]: (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_7)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_10])).
% 1.71/1.14  tff(c_222, plain, (![A_7]: (k1_tarski(A_7)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_14, c_16, c_32, c_219])).
% 1.71/1.14  tff(c_227, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_222])).
% 1.71/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  Inference rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Ref     : 1
% 1.71/1.14  #Sup     : 50
% 1.71/1.14  #Fact    : 0
% 1.71/1.14  #Define  : 0
% 1.71/1.14  #Split   : 0
% 1.71/1.14  #Chain   : 0
% 1.71/1.14  #Close   : 0
% 1.71/1.14  
% 1.71/1.14  Ordering : KBO
% 1.71/1.14  
% 1.71/1.14  Simplification rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Subsume      : 6
% 1.71/1.14  #Demod        : 14
% 1.71/1.14  #Tautology    : 35
% 1.71/1.14  #SimpNegUnit  : 1
% 1.71/1.14  #BackRed      : 0
% 1.71/1.14  
% 1.71/1.14  #Partial instantiations: 0
% 1.71/1.14  #Strategies tried      : 1
% 1.71/1.14  
% 1.71/1.14  Timing (in seconds)
% 1.71/1.14  ----------------------
% 1.71/1.14  Preprocessing        : 0.26
% 1.71/1.15  Parsing              : 0.14
% 1.71/1.15  CNF conversion       : 0.01
% 1.71/1.15  Main loop            : 0.13
% 1.71/1.15  Inferencing          : 0.05
% 1.71/1.15  Reduction            : 0.05
% 1.71/1.15  Demodulation         : 0.04
% 1.71/1.15  BG Simplification    : 0.01
% 1.71/1.15  Subsumption          : 0.02
% 1.71/1.15  Abstraction          : 0.01
% 1.71/1.15  MUC search           : 0.00
% 1.71/1.15  Cooper               : 0.00
% 1.71/1.15  Total                : 0.42
% 1.71/1.15  Index Insertion      : 0.00
% 1.71/1.15  Index Deletion       : 0.00
% 1.71/1.15  Index Matching       : 0.00
% 1.71/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
