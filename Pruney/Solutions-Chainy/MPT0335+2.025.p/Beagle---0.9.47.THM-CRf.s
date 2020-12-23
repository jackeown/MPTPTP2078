%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  47 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_44,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1543,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0(k1_tarski(A_120),B_121) = k1_tarski(A_120)
      | ~ r2_hidden(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_135,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1651,plain,(
    ! [B_122,A_123] :
      ( k3_xboole_0(B_122,k1_tarski(A_123)) = k1_tarski(A_123)
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1543,c_2])).

tff(c_48,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_117,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_121,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_477,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(k3_xboole_0(A_82,B_83),C_84) = k3_xboole_0(A_82,k3_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_546,plain,(
    ! [C_85] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_85)) = k3_xboole_0('#skF_4',C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_477])).

tff(c_582,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_546])).

tff(c_1693,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1651,c_582])).

tff(c_1776,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1693])).

tff(c_1778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.54/1.59  
% 3.54/1.59  %Foreground sorts:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Background operators:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Foreground operators:
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.59  
% 3.54/1.60  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 3.54/1.60  tff(f_62, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.54/1.60  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/1.60  tff(f_46, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.54/1.60  tff(c_44, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.60  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.60  tff(c_135, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.54/1.60  tff(c_30, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.60  tff(c_1543, plain, (![A_120, B_121]: (k3_xboole_0(k1_tarski(A_120), B_121)=k1_tarski(A_120) | ~r2_hidden(A_120, B_121))), inference(resolution, [status(thm)], [c_135, c_30])).
% 3.54/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.60  tff(c_1651, plain, (![B_122, A_123]: (k3_xboole_0(B_122, k1_tarski(A_123))=k1_tarski(A_123) | ~r2_hidden(A_123, B_122))), inference(superposition, [status(thm), theory('equality')], [c_1543, c_2])).
% 3.54/1.60  tff(c_48, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.60  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.60  tff(c_117, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.60  tff(c_121, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_117])).
% 3.54/1.60  tff(c_477, plain, (![A_82, B_83, C_84]: (k3_xboole_0(k3_xboole_0(A_82, B_83), C_84)=k3_xboole_0(A_82, k3_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.54/1.60  tff(c_546, plain, (![C_85]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_85))=k3_xboole_0('#skF_4', C_85))), inference(superposition, [status(thm), theory('equality')], [c_121, c_477])).
% 3.54/1.60  tff(c_582, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_48, c_546])).
% 3.54/1.60  tff(c_1693, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1651, c_582])).
% 3.54/1.60  tff(c_1776, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1693])).
% 3.54/1.60  tff(c_1778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1776])).
% 3.54/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.60  
% 3.54/1.60  Inference rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Ref     : 0
% 3.54/1.60  #Sup     : 439
% 3.54/1.60  #Fact    : 0
% 3.54/1.60  #Define  : 0
% 3.54/1.60  #Split   : 0
% 3.54/1.60  #Chain   : 0
% 3.54/1.60  #Close   : 0
% 3.54/1.60  
% 3.54/1.60  Ordering : KBO
% 3.54/1.60  
% 3.54/1.60  Simplification rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Subsume      : 52
% 3.54/1.60  #Demod        : 229
% 3.54/1.60  #Tautology    : 187
% 3.54/1.60  #SimpNegUnit  : 1
% 3.54/1.60  #BackRed      : 0
% 3.54/1.60  
% 3.54/1.60  #Partial instantiations: 0
% 3.54/1.60  #Strategies tried      : 1
% 3.54/1.60  
% 3.54/1.60  Timing (in seconds)
% 3.54/1.60  ----------------------
% 3.54/1.60  Preprocessing        : 0.31
% 3.54/1.60  Parsing              : 0.16
% 3.54/1.60  CNF conversion       : 0.02
% 3.54/1.60  Main loop            : 0.52
% 3.54/1.60  Inferencing          : 0.16
% 3.54/1.60  Reduction            : 0.21
% 3.54/1.60  Demodulation         : 0.17
% 3.54/1.60  BG Simplification    : 0.03
% 3.54/1.60  Subsumption          : 0.09
% 3.54/1.60  Abstraction          : 0.02
% 3.54/1.60  MUC search           : 0.00
% 3.54/1.60  Cooper               : 0.00
% 3.54/1.60  Total                : 0.86
% 3.54/1.60  Index Insertion      : 0.00
% 3.54/1.60  Index Deletion       : 0.00
% 3.54/1.60  Index Matching       : 0.00
% 3.54/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
