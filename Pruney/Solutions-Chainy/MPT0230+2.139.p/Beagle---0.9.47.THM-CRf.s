%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:13 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_159,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | k4_xboole_0(k1_tarski(A_69),B_70) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_170,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_159])).

tff(c_218,plain,(
    ! [D_78,B_79,A_80] :
      ( D_78 = B_79
      | D_78 = A_80
      | ~ r2_hidden(D_78,k2_tarski(A_80,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_221,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_170,c_218])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.11/1.23  
% 2.11/1.23  %Foreground sorts:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Background operators:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Foreground operators:
% 2.11/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  
% 2.16/1.24  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.16/1.24  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.16/1.24  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.16/1.24  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.16/1.24  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.24  tff(c_50, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.24  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.24  tff(c_84, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.24  tff(c_91, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_84])).
% 2.16/1.24  tff(c_159, plain, (![A_69, B_70]: (r2_hidden(A_69, B_70) | k4_xboole_0(k1_tarski(A_69), B_70)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.24  tff(c_170, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_159])).
% 2.16/1.24  tff(c_218, plain, (![D_78, B_79, A_80]: (D_78=B_79 | D_78=A_80 | ~r2_hidden(D_78, k2_tarski(A_80, B_79)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.24  tff(c_221, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_170, c_218])).
% 2.16/1.24  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_221])).
% 2.16/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  Inference rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Ref     : 0
% 2.16/1.24  #Sup     : 42
% 2.16/1.24  #Fact    : 0
% 2.16/1.24  #Define  : 0
% 2.16/1.24  #Split   : 0
% 2.16/1.24  #Chain   : 0
% 2.16/1.24  #Close   : 0
% 2.16/1.24  
% 2.16/1.24  Ordering : KBO
% 2.16/1.24  
% 2.16/1.24  Simplification rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Subsume      : 0
% 2.16/1.24  #Demod        : 7
% 2.16/1.24  #Tautology    : 29
% 2.16/1.24  #SimpNegUnit  : 1
% 2.16/1.24  #BackRed      : 0
% 2.16/1.24  
% 2.16/1.24  #Partial instantiations: 0
% 2.16/1.24  #Strategies tried      : 1
% 2.16/1.24  
% 2.16/1.24  Timing (in seconds)
% 2.16/1.24  ----------------------
% 2.16/1.24  Preprocessing        : 0.33
% 2.16/1.24  Parsing              : 0.18
% 2.16/1.24  CNF conversion       : 0.02
% 2.16/1.24  Main loop            : 0.15
% 2.16/1.24  Inferencing          : 0.05
% 2.16/1.24  Reduction            : 0.05
% 2.16/1.24  Demodulation         : 0.04
% 2.16/1.24  BG Simplification    : 0.01
% 2.16/1.24  Subsumption          : 0.02
% 2.16/1.24  Abstraction          : 0.01
% 2.16/1.24  MUC search           : 0.00
% 2.16/1.24  Cooper               : 0.00
% 2.16/1.24  Total                : 0.50
% 2.16/1.24  Index Insertion      : 0.00
% 2.16/1.24  Index Deletion       : 0.00
% 2.16/1.24  Index Matching       : 0.00
% 2.16/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
