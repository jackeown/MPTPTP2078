%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:12 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  62 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 113 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_33,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_21,c_10])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_11,C_12,B_13] :
      ( r2_xboole_0(A_11,C_12)
      | ~ r2_xboole_0(B_13,C_12)
      | ~ r2_xboole_0(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_16,B_17,A_18] :
      ( r2_xboole_0(A_16,B_17)
      | ~ r2_xboole_0(A_16,A_18)
      | B_17 = A_18
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_78,plain,(
    ! [B_19] :
      ( r2_xboole_0('#skF_1',B_19)
      | B_19 = '#skF_2'
      | ~ r1_tarski('#skF_2',B_19) ) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_92,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_10])).

tff(c_104,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_111,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_111])).

tff(c_116,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_119,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_12])).

tff(c_125,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_xboole_0(A_20,C_21)
      | ~ r2_xboole_0(B_22,C_21)
      | ~ r2_xboole_0(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_23] :
      ( r2_xboole_0(A_23,'#skF_2')
      | ~ r2_xboole_0(A_23,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_144,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_147,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_144])).

tff(c_150,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_147])).

tff(c_155,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.17  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  
% 1.78/1.18  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.78/1.18  tff(f_45, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.78/1.18  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_xboole_1)).
% 1.78/1.18  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.18  tff(c_21, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.18  tff(c_10, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.18  tff(c_33, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_21, c_10])).
% 1.78/1.18  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_33])).
% 1.78/1.18  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.18  tff(c_14, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.18  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.18  tff(c_37, plain, (![A_11, C_12, B_13]: (r2_xboole_0(A_11, C_12) | ~r2_xboole_0(B_13, C_12) | ~r2_xboole_0(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.18  tff(c_68, plain, (![A_16, B_17, A_18]: (r2_xboole_0(A_16, B_17) | ~r2_xboole_0(A_16, A_18) | B_17=A_18 | ~r1_tarski(A_18, B_17))), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.78/1.18  tff(c_78, plain, (![B_19]: (r2_xboole_0('#skF_1', B_19) | B_19='#skF_2' | ~r1_tarski('#skF_2', B_19))), inference(resolution, [status(thm)], [c_14, c_68])).
% 1.78/1.18  tff(c_92, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_10])).
% 1.78/1.18  tff(c_104, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 1.78/1.18  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.18  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_16])).
% 1.78/1.18  tff(c_111, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_20])).
% 1.78/1.18  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_111])).
% 1.78/1.18  tff(c_116, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_33])).
% 1.78/1.18  tff(c_119, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_12])).
% 1.78/1.18  tff(c_125, plain, (![A_20, C_21, B_22]: (r2_xboole_0(A_20, C_21) | ~r2_xboole_0(B_22, C_21) | ~r2_xboole_0(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.18  tff(c_132, plain, (![A_23]: (r2_xboole_0(A_23, '#skF_2') | ~r2_xboole_0(A_23, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_125])).
% 1.78/1.18  tff(c_144, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_132, c_4])).
% 1.78/1.18  tff(c_147, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_2, c_144])).
% 1.78/1.18  tff(c_150, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_147])).
% 1.78/1.18  tff(c_155, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_14])).
% 1.78/1.18  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_155])).
% 1.78/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  Inference rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Ref     : 0
% 1.78/1.18  #Sup     : 28
% 1.78/1.18  #Fact    : 0
% 1.78/1.18  #Define  : 0
% 1.78/1.18  #Split   : 2
% 1.78/1.18  #Chain   : 0
% 1.78/1.18  #Close   : 0
% 1.78/1.18  
% 1.78/1.18  Ordering : KBO
% 1.78/1.18  
% 1.78/1.18  Simplification rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Subsume      : 4
% 1.78/1.18  #Demod        : 22
% 1.78/1.18  #Tautology    : 7
% 1.78/1.18  #SimpNegUnit  : 2
% 1.78/1.18  #BackRed      : 14
% 1.78/1.18  
% 1.78/1.18  #Partial instantiations: 0
% 1.78/1.18  #Strategies tried      : 1
% 1.78/1.18  
% 1.78/1.18  Timing (in seconds)
% 1.78/1.18  ----------------------
% 1.78/1.18  Preprocessing        : 0.24
% 1.78/1.18  Parsing              : 0.13
% 1.78/1.18  CNF conversion       : 0.02
% 1.78/1.18  Main loop            : 0.17
% 1.78/1.18  Inferencing          : 0.06
% 1.78/1.18  Reduction            : 0.04
% 1.78/1.18  Demodulation         : 0.03
% 1.78/1.18  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.04
% 1.78/1.19  Abstraction          : 0.01
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.44
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
