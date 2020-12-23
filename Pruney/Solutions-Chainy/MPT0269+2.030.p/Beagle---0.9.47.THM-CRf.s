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
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  69 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_794,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,k1_tarski(B_90)) = A_89
      | r2_hidden(B_90,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_827,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_60])).

tff(c_860,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_827])).

tff(c_36,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_3541,plain,(
    ! [B_207,B_208] :
      ( k4_xboole_0(k1_tarski(B_207),B_208) = k1_xboole_0
      | r2_hidden(B_207,k4_xboole_0(k1_tarski(B_207),B_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_133])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3705,plain,(
    ! [B_211,B_212] :
      ( ~ r2_hidden(B_211,B_212)
      | k4_xboole_0(k1_tarski(B_211),B_212) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3541,c_4])).

tff(c_56,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_640,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1651,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(B_127,A_128)
      | k4_xboole_0(A_128,B_127) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_640])).

tff(c_2421,plain,(
    ! [B_168,A_169] :
      ( B_168 = A_169
      | k4_xboole_0(B_168,A_169) != k1_xboole_0
      | k4_xboole_0(A_169,B_168) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_1651])).

tff(c_2437,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2421])).

tff(c_2456,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2437])).

tff(c_3727,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3705,c_2456])).

tff(c_3850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_3727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n021.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 10:52:34 EST 2020
% 0.12/0.30  % CPUTime    : 
% 0.12/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.69  
% 4.09/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.69  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.09/1.69  
% 4.09/1.69  %Foreground sorts:
% 4.09/1.69  
% 4.09/1.69  
% 4.09/1.69  %Background operators:
% 4.09/1.69  
% 4.09/1.69  
% 4.09/1.69  %Foreground operators:
% 4.09/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.09/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.09/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.09/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.09/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.09/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.09/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.09/1.69  
% 4.09/1.70  tff(f_82, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.09/1.70  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.09/1.70  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.09/1.70  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.09/1.70  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.09/1.70  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.09/1.70  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.70  tff(c_794, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k1_tarski(B_90))=A_89 | r2_hidden(B_90, A_89))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.09/1.70  tff(c_60, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.70  tff(c_827, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_794, c_60])).
% 4.09/1.70  tff(c_860, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_827])).
% 4.09/1.70  tff(c_36, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.09/1.70  tff(c_121, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.70  tff(c_133, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_121])).
% 4.09/1.70  tff(c_3541, plain, (![B_207, B_208]: (k4_xboole_0(k1_tarski(B_207), B_208)=k1_xboole_0 | r2_hidden(B_207, k4_xboole_0(k1_tarski(B_207), B_208)))), inference(superposition, [status(thm), theory('equality')], [c_794, c_133])).
% 4.09/1.70  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.70  tff(c_3705, plain, (![B_211, B_212]: (~r2_hidden(B_211, B_212) | k4_xboole_0(k1_tarski(B_211), B_212)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3541, c_4])).
% 4.09/1.70  tff(c_56, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.70  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.70  tff(c_640, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.70  tff(c_1651, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(B_127, A_128) | k4_xboole_0(A_128, B_127)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_640])).
% 4.09/1.70  tff(c_2421, plain, (![B_168, A_169]: (B_168=A_169 | k4_xboole_0(B_168, A_169)!=k1_xboole_0 | k4_xboole_0(A_169, B_168)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_1651])).
% 4.09/1.70  tff(c_2437, plain, (k1_tarski('#skF_4')='#skF_3' | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_2421])).
% 4.09/1.70  tff(c_2456, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_2437])).
% 4.09/1.70  tff(c_3727, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3705, c_2456])).
% 4.09/1.70  tff(c_3850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_860, c_3727])).
% 4.09/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.70  
% 4.09/1.70  Inference rules
% 4.09/1.70  ----------------------
% 4.09/1.70  #Ref     : 0
% 4.09/1.70  #Sup     : 889
% 4.09/1.70  #Fact    : 0
% 4.09/1.70  #Define  : 0
% 4.09/1.70  #Split   : 2
% 4.09/1.70  #Chain   : 0
% 4.09/1.70  #Close   : 0
% 4.09/1.70  
% 4.09/1.70  Ordering : KBO
% 4.09/1.70  
% 4.09/1.70  Simplification rules
% 4.09/1.70  ----------------------
% 4.09/1.70  #Subsume      : 154
% 4.09/1.70  #Demod        : 609
% 4.09/1.70  #Tautology    : 478
% 4.09/1.70  #SimpNegUnit  : 35
% 4.09/1.70  #BackRed      : 6
% 4.09/1.70  
% 4.09/1.70  #Partial instantiations: 0
% 4.09/1.70  #Strategies tried      : 1
% 4.09/1.70  
% 4.09/1.70  Timing (in seconds)
% 4.09/1.70  ----------------------
% 4.09/1.71  Preprocessing        : 0.33
% 4.09/1.71  Parsing              : 0.17
% 4.09/1.71  CNF conversion       : 0.02
% 4.09/1.71  Main loop            : 0.72
% 4.09/1.71  Inferencing          : 0.24
% 4.09/1.71  Reduction            : 0.28
% 4.09/1.71  Demodulation         : 0.21
% 4.09/1.71  BG Simplification    : 0.03
% 4.09/1.71  Subsumption          : 0.13
% 4.09/1.71  Abstraction          : 0.04
% 4.09/1.71  MUC search           : 0.00
% 4.09/1.71  Cooper               : 0.00
% 4.09/1.71  Total                : 1.07
% 4.09/1.71  Index Insertion      : 0.00
% 4.09/1.71  Index Deletion       : 0.00
% 4.09/1.71  Index Matching       : 0.00
% 4.09/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
