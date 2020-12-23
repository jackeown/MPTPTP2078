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
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 24.73s
% Output     : CNFRefutation 24.73s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  62 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_111,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_96,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_515,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_3'(A_105,B_106),A_105)
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [C_41,A_37] :
      ( C_41 = A_37
      | ~ r2_hidden(C_41,k1_tarski(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4726,plain,(
    ! [A_296,B_297] :
      ( '#skF_3'(k1_tarski(A_296),B_297) = A_296
      | r1_xboole_0(k1_tarski(A_296),B_297) ) ),
    inference(resolution,[status(thm)],[c_515,c_74])).

tff(c_4760,plain,(
    '#skF_3'(k1_tarski('#skF_9'),'#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4726,c_96])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4767,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4760,c_28])).

tff(c_4772,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_4767])).

tff(c_86,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1450,plain,(
    ! [A_172,C_173,B_174] :
      ( k3_xboole_0(k2_tarski(A_172,C_173),B_174) = k2_tarski(A_172,C_173)
      | ~ r2_hidden(C_173,B_174)
      | ~ r2_hidden(A_172,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1524,plain,(
    ! [A_42,B_174] :
      ( k3_xboole_0(k1_tarski(A_42),B_174) = k2_tarski(A_42,A_42)
      | ~ r2_hidden(A_42,B_174)
      | ~ r2_hidden(A_42,B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1450])).

tff(c_11266,plain,(
    ! [A_441,B_442] :
      ( k3_xboole_0(k1_tarski(A_441),B_442) = k1_tarski(A_441)
      | ~ r2_hidden(A_441,B_442)
      | ~ r2_hidden(A_441,B_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1524])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103880,plain,(
    ! [B_20972,A_20973] :
      ( k3_xboole_0(B_20972,k1_tarski(A_20973)) = k1_tarski(A_20973)
      | ~ r2_hidden(A_20973,B_20972)
      | ~ r2_hidden(A_20973,B_20972) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11266,c_2])).

tff(c_94,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),'#skF_10') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_97,plain,(
    k3_xboole_0('#skF_10',k1_tarski('#skF_9')) != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_104671,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_103880,c_97])).

tff(c_104978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4772,c_104671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.73/15.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/15.34  
% 24.73/15.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/15.34  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7 > #skF_4
% 24.73/15.34  
% 24.73/15.34  %Foreground sorts:
% 24.73/15.34  
% 24.73/15.34  
% 24.73/15.34  %Background operators:
% 24.73/15.34  
% 24.73/15.34  
% 24.73/15.34  %Foreground operators:
% 24.73/15.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 24.73/15.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.73/15.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.73/15.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.73/15.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.73/15.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.73/15.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 24.73/15.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 24.73/15.34  tff('#skF_10', type, '#skF_10': $i).
% 24.73/15.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.73/15.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.73/15.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.73/15.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.73/15.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 24.73/15.34  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 24.73/15.34  tff('#skF_9', type, '#skF_9': $i).
% 24.73/15.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.73/15.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 24.73/15.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.73/15.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.73/15.34  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 24.73/15.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 24.73/15.34  
% 24.73/15.35  tff(f_126, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 24.73/15.35  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 24.73/15.35  tff(f_109, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 24.73/15.35  tff(f_111, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 24.73/15.35  tff(f_121, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 24.73/15.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.73/15.35  tff(c_96, plain, (~r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_126])).
% 24.73/15.35  tff(c_515, plain, (![A_105, B_106]: (r2_hidden('#skF_3'(A_105, B_106), A_105) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.73/15.35  tff(c_74, plain, (![C_41, A_37]: (C_41=A_37 | ~r2_hidden(C_41, k1_tarski(A_37)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.73/15.35  tff(c_4726, plain, (![A_296, B_297]: ('#skF_3'(k1_tarski(A_296), B_297)=A_296 | r1_xboole_0(k1_tarski(A_296), B_297))), inference(resolution, [status(thm)], [c_515, c_74])).
% 24.73/15.35  tff(c_4760, plain, ('#skF_3'(k1_tarski('#skF_9'), '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_4726, c_96])).
% 24.73/15.35  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.73/15.35  tff(c_4767, plain, (r2_hidden('#skF_9', '#skF_10') | r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4760, c_28])).
% 24.73/15.35  tff(c_4772, plain, (r2_hidden('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_96, c_4767])).
% 24.73/15.35  tff(c_86, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 24.73/15.35  tff(c_1450, plain, (![A_172, C_173, B_174]: (k3_xboole_0(k2_tarski(A_172, C_173), B_174)=k2_tarski(A_172, C_173) | ~r2_hidden(C_173, B_174) | ~r2_hidden(A_172, B_174))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.73/15.35  tff(c_1524, plain, (![A_42, B_174]: (k3_xboole_0(k1_tarski(A_42), B_174)=k2_tarski(A_42, A_42) | ~r2_hidden(A_42, B_174) | ~r2_hidden(A_42, B_174))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1450])).
% 24.73/15.35  tff(c_11266, plain, (![A_441, B_442]: (k3_xboole_0(k1_tarski(A_441), B_442)=k1_tarski(A_441) | ~r2_hidden(A_441, B_442) | ~r2_hidden(A_441, B_442))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1524])).
% 24.73/15.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.73/15.35  tff(c_103880, plain, (![B_20972, A_20973]: (k3_xboole_0(B_20972, k1_tarski(A_20973))=k1_tarski(A_20973) | ~r2_hidden(A_20973, B_20972) | ~r2_hidden(A_20973, B_20972))), inference(superposition, [status(thm), theory('equality')], [c_11266, c_2])).
% 24.73/15.35  tff(c_94, plain, (k3_xboole_0(k1_tarski('#skF_9'), '#skF_10')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 24.73/15.35  tff(c_97, plain, (k3_xboole_0('#skF_10', k1_tarski('#skF_9'))!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_94])).
% 24.73/15.35  tff(c_104671, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_103880, c_97])).
% 24.73/15.35  tff(c_104978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4772, c_104671])).
% 24.73/15.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/15.35  
% 24.73/15.35  Inference rules
% 24.73/15.35  ----------------------
% 24.73/15.35  #Ref     : 4
% 24.73/15.35  #Sup     : 25441
% 24.73/15.35  #Fact    : 18
% 24.73/15.35  #Define  : 0
% 24.73/15.35  #Split   : 2
% 24.73/15.35  #Chain   : 0
% 24.73/15.35  #Close   : 0
% 24.73/15.35  
% 24.73/15.35  Ordering : KBO
% 24.73/15.35  
% 24.73/15.35  Simplification rules
% 24.73/15.35  ----------------------
% 24.73/15.35  #Subsume      : 9998
% 24.73/15.35  #Demod        : 16301
% 24.73/15.35  #Tautology    : 8913
% 24.73/15.35  #SimpNegUnit  : 834
% 24.73/15.35  #BackRed      : 0
% 24.73/15.35  
% 24.73/15.35  #Partial instantiations: 9248
% 24.73/15.35  #Strategies tried      : 1
% 24.73/15.35  
% 24.73/15.35  Timing (in seconds)
% 24.73/15.35  ----------------------
% 24.73/15.35  Preprocessing        : 0.38
% 24.73/15.35  Parsing              : 0.17
% 24.73/15.35  CNF conversion       : 0.03
% 24.73/15.35  Main loop            : 14.18
% 24.73/15.35  Inferencing          : 2.03
% 24.73/15.35  Reduction            : 7.01
% 24.73/15.35  Demodulation         : 5.79
% 24.73/15.35  BG Simplification    : 0.20
% 24.73/15.35  Subsumption          : 4.32
% 24.73/15.35  Abstraction          : 0.38
% 24.73/15.35  MUC search           : 0.00
% 24.73/15.35  Cooper               : 0.00
% 24.73/15.35  Total                : 14.59
% 24.73/15.35  Index Insertion      : 0.00
% 24.73/15.35  Index Deletion       : 0.00
% 24.73/15.35  Index Matching       : 0.00
% 24.73/15.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
