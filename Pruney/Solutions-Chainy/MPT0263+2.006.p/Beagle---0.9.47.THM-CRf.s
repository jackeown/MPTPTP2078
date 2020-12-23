%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 28.89s
% Output     : CNFRefutation 28.89s
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

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_113,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_96,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_313,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_3'(A_90,B_91),A_90)
      | r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,(
    ! [C_42,A_38] :
      ( C_42 = A_38
      | ~ r2_hidden(C_42,k1_tarski(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5204,plain,(
    ! [A_303,B_304] :
      ( '#skF_3'(k1_tarski(A_303),B_304) = A_303
      | r1_xboole_0(k1_tarski(A_303),B_304) ) ),
    inference(resolution,[status(thm)],[c_313,c_74])).

tff(c_5238,plain,(
    '#skF_3'(k1_tarski('#skF_9'),'#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5204,c_96])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5242,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5238,c_30])).

tff(c_5248,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_5242])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1367,plain,(
    ! [A_169,C_170,B_171] :
      ( k3_xboole_0(k2_tarski(A_169,C_170),B_171) = k2_tarski(A_169,C_170)
      | ~ r2_hidden(C_170,B_171)
      | ~ r2_hidden(A_169,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1435,plain,(
    ! [A_43,B_171] :
      ( k3_xboole_0(k1_tarski(A_43),B_171) = k2_tarski(A_43,A_43)
      | ~ r2_hidden(A_43,B_171)
      | ~ r2_hidden(A_43,B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1367])).

tff(c_10843,plain,(
    ! [A_437,B_438] :
      ( k3_xboole_0(k1_tarski(A_437),B_438) = k1_tarski(A_437)
      | ~ r2_hidden(A_437,B_438)
      | ~ r2_hidden(A_437,B_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1435])).

tff(c_113073,plain,(
    ! [A_22279,A_22280] :
      ( k3_xboole_0(A_22279,k1_tarski(A_22280)) = k1_tarski(A_22280)
      | ~ r2_hidden(A_22280,A_22279)
      | ~ r2_hidden(A_22280,A_22279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10843])).

tff(c_94,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),'#skF_10') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_97,plain,(
    k3_xboole_0('#skF_10',k1_tarski('#skF_9')) != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_113906,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_113073,c_97])).

tff(c_114173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5248,c_113906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n011.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:16:27 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.89/18.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.89/18.68  
% 28.89/18.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.89/18.68  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7 > #skF_4
% 28.89/18.68  
% 28.89/18.68  %Foreground sorts:
% 28.89/18.68  
% 28.89/18.68  
% 28.89/18.68  %Background operators:
% 28.89/18.68  
% 28.89/18.68  
% 28.89/18.68  %Foreground operators:
% 28.89/18.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 28.89/18.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.89/18.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.89/18.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 28.89/18.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.89/18.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.89/18.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 28.89/18.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 28.89/18.68  tff('#skF_10', type, '#skF_10': $i).
% 28.89/18.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 28.89/18.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 28.89/18.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 28.89/18.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.89/18.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 28.89/18.68  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 28.89/18.68  tff('#skF_9', type, '#skF_9': $i).
% 28.89/18.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.89/18.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 28.89/18.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.89/18.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.89/18.68  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 28.89/18.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.89/18.68  
% 28.89/18.69  tff(f_128, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 28.89/18.69  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 28.89/18.69  tff(f_111, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 28.89/18.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 28.89/18.69  tff(f_113, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 28.89/18.69  tff(f_123, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 28.89/18.69  tff(c_96, plain, (~r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_128])).
% 28.89/18.69  tff(c_313, plain, (![A_90, B_91]: (r2_hidden('#skF_3'(A_90, B_91), A_90) | r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_63])).
% 28.89/18.69  tff(c_74, plain, (![C_42, A_38]: (C_42=A_38 | ~r2_hidden(C_42, k1_tarski(A_38)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.89/18.69  tff(c_5204, plain, (![A_303, B_304]: ('#skF_3'(k1_tarski(A_303), B_304)=A_303 | r1_xboole_0(k1_tarski(A_303), B_304))), inference(resolution, [status(thm)], [c_313, c_74])).
% 28.89/18.69  tff(c_5238, plain, ('#skF_3'(k1_tarski('#skF_9'), '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_5204, c_96])).
% 28.89/18.69  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 28.89/18.69  tff(c_5242, plain, (r2_hidden('#skF_9', '#skF_10') | r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5238, c_30])).
% 28.89/18.69  tff(c_5248, plain, (r2_hidden('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_96, c_5242])).
% 28.89/18.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.89/18.69  tff(c_86, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_113])).
% 28.89/18.69  tff(c_1367, plain, (![A_169, C_170, B_171]: (k3_xboole_0(k2_tarski(A_169, C_170), B_171)=k2_tarski(A_169, C_170) | ~r2_hidden(C_170, B_171) | ~r2_hidden(A_169, B_171))), inference(cnfTransformation, [status(thm)], [f_123])).
% 28.89/18.69  tff(c_1435, plain, (![A_43, B_171]: (k3_xboole_0(k1_tarski(A_43), B_171)=k2_tarski(A_43, A_43) | ~r2_hidden(A_43, B_171) | ~r2_hidden(A_43, B_171))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1367])).
% 28.89/18.69  tff(c_10843, plain, (![A_437, B_438]: (k3_xboole_0(k1_tarski(A_437), B_438)=k1_tarski(A_437) | ~r2_hidden(A_437, B_438) | ~r2_hidden(A_437, B_438))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1435])).
% 28.89/18.69  tff(c_113073, plain, (![A_22279, A_22280]: (k3_xboole_0(A_22279, k1_tarski(A_22280))=k1_tarski(A_22280) | ~r2_hidden(A_22280, A_22279) | ~r2_hidden(A_22280, A_22279))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10843])).
% 28.89/18.69  tff(c_94, plain, (k3_xboole_0(k1_tarski('#skF_9'), '#skF_10')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_128])).
% 28.89/18.69  tff(c_97, plain, (k3_xboole_0('#skF_10', k1_tarski('#skF_9'))!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_94])).
% 28.89/18.69  tff(c_113906, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_113073, c_97])).
% 28.89/18.69  tff(c_114173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5248, c_113906])).
% 28.89/18.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.89/18.69  
% 28.89/18.69  Inference rules
% 28.89/18.69  ----------------------
% 28.89/18.69  #Ref     : 5
% 28.89/18.69  #Sup     : 27668
% 28.89/18.69  #Fact    : 18
% 28.89/18.69  #Define  : 0
% 28.89/18.69  #Split   : 2
% 28.89/18.69  #Chain   : 0
% 28.89/18.69  #Close   : 0
% 28.89/18.69  
% 28.89/18.69  Ordering : KBO
% 28.89/18.69  
% 28.89/18.69  Simplification rules
% 28.89/18.69  ----------------------
% 28.89/18.69  #Subsume      : 10641
% 28.89/18.69  #Demod        : 19616
% 28.89/18.69  #Tautology    : 9147
% 28.89/18.69  #SimpNegUnit  : 890
% 28.89/18.69  #BackRed      : 0
% 28.89/18.69  
% 28.89/18.69  #Partial instantiations: 9809
% 28.89/18.69  #Strategies tried      : 1
% 28.89/18.69  
% 28.89/18.69  Timing (in seconds)
% 28.89/18.69  ----------------------
% 28.89/18.70  Preprocessing        : 0.36
% 28.89/18.70  Parsing              : 0.18
% 28.89/18.70  CNF conversion       : 0.03
% 28.89/18.70  Main loop            : 17.60
% 28.89/18.70  Inferencing          : 2.33
% 28.89/18.70  Reduction            : 8.63
% 28.89/18.70  Demodulation         : 7.22
% 28.89/18.70  BG Simplification    : 0.24
% 28.89/18.70  Subsumption          : 5.66
% 28.89/18.70  Abstraction          : 0.46
% 28.89/18.70  MUC search           : 0.00
% 28.89/18.70  Cooper               : 0.00
% 28.89/18.70  Total                : 17.99
% 28.89/18.70  Index Insertion      : 0.00
% 28.89/18.70  Index Deletion       : 0.00
% 28.89/18.70  Index Matching       : 0.00
% 28.89/18.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
