%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   24 (  31 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k1_tarski(A_13),B_14) = k1_tarski(A_13)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [B_6] : k4_xboole_0(k1_tarski(B_6),k1_tarski(B_6)) != k1_tarski(B_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(k1_tarski(A_8),B_9) = k1_xboole_0
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29,plain,(
    ! [A_8] :
      ( k1_tarski(A_8) != k1_xboole_0
      | ~ r2_hidden(A_8,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_10])).

tff(c_85,plain,(
    ! [A_8] : k1_tarski(A_8) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_29])).

tff(c_102,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k1_tarski(A_19)
      | B_20 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_16])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_85,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.15  
% 1.58/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.15  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.58/1.15  
% 1.58/1.15  %Foreground sorts:
% 1.58/1.15  
% 1.58/1.15  
% 1.58/1.15  %Background operators:
% 1.58/1.15  
% 1.58/1.15  
% 1.58/1.15  %Foreground operators:
% 1.58/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.58/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.15  
% 1.58/1.16  tff(f_44, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.58/1.16  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.58/1.16  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.58/1.16  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.58/1.16  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.58/1.16  tff(c_53, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), B_14)=k1_tarski(A_13) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.58/1.16  tff(c_10, plain, (![B_6]: (k4_xboole_0(k1_tarski(B_6), k1_tarski(B_6))!=k1_tarski(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.16  tff(c_80, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 1.58/1.16  tff(c_22, plain, (![A_8, B_9]: (k4_xboole_0(k1_tarski(A_8), B_9)=k1_xboole_0 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.16  tff(c_29, plain, (![A_8]: (k1_tarski(A_8)!=k1_xboole_0 | ~r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_10])).
% 1.58/1.16  tff(c_85, plain, (![A_8]: (k1_tarski(A_8)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_29])).
% 1.58/1.16  tff(c_102, plain, (![A_19, B_20]: (k4_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k1_tarski(A_19) | B_20=A_19)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.16  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.58/1.16  tff(c_124, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_102, c_16])).
% 1.58/1.16  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_85, c_124])).
% 1.58/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.16  
% 1.58/1.16  Inference rules
% 1.58/1.16  ----------------------
% 1.58/1.16  #Ref     : 0
% 1.58/1.16  #Sup     : 31
% 1.58/1.16  #Fact    : 0
% 1.58/1.16  #Define  : 0
% 1.58/1.16  #Split   : 0
% 1.58/1.16  #Chain   : 0
% 1.58/1.16  #Close   : 0
% 1.58/1.16  
% 1.58/1.16  Ordering : KBO
% 1.58/1.16  
% 1.58/1.16  Simplification rules
% 1.58/1.16  ----------------------
% 1.58/1.16  #Subsume      : 2
% 1.58/1.16  #Demod        : 4
% 1.58/1.16  #Tautology    : 17
% 1.58/1.16  #SimpNegUnit  : 2
% 1.58/1.16  #BackRed      : 1
% 1.58/1.16  
% 1.58/1.16  #Partial instantiations: 0
% 1.58/1.16  #Strategies tried      : 1
% 1.58/1.16  
% 1.58/1.16  Timing (in seconds)
% 1.58/1.16  ----------------------
% 1.58/1.16  Preprocessing        : 0.26
% 1.58/1.16  Parsing              : 0.14
% 1.58/1.16  CNF conversion       : 0.01
% 1.58/1.16  Main loop            : 0.10
% 1.58/1.16  Inferencing          : 0.05
% 1.58/1.16  Reduction            : 0.03
% 1.58/1.16  Demodulation         : 0.02
% 1.58/1.16  BG Simplification    : 0.01
% 1.58/1.16  Subsumption          : 0.01
% 1.58/1.16  Abstraction          : 0.01
% 1.58/1.16  MUC search           : 0.00
% 1.58/1.16  Cooper               : 0.00
% 1.58/1.16  Total                : 0.39
% 1.58/1.16  Index Insertion      : 0.00
% 1.58/1.16  Index Deletion       : 0.00
% 1.58/1.16  Index Matching       : 0.00
% 1.58/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
