%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_16,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    ! [B_8,A_9] :
      ( r1_xboole_0(B_8,A_9)
      | ~ r1_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_35,plain,(
    ! [A_10,C_11,B_12] :
      ( r1_xboole_0(A_10,C_11)
      | ~ r1_xboole_0(B_12,C_11)
      | ~ r1_tarski(A_10,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [A_17] :
      ( r1_xboole_0(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_114,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.16  
% 1.63/1.17  tff(f_57, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.63/1.17  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.63/1.17  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.63/1.17  tff(f_48, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.63/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.17  tff(c_16, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.63/1.17  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.63/1.17  tff(c_12, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.63/1.17  tff(c_23, plain, (![B_8, A_9]: (r1_xboole_0(B_8, A_9) | ~r1_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.63/1.17  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.63/1.17  tff(c_35, plain, (![A_10, C_11, B_12]: (r1_xboole_0(A_10, C_11) | ~r1_xboole_0(B_12, C_11) | ~r1_tarski(A_10, B_12))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.63/1.17  tff(c_96, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_35])).
% 1.63/1.17  tff(c_10, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.17  tff(c_104, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_96, c_10])).
% 1.63/1.17  tff(c_109, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_104])).
% 1.63/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.63/1.17  tff(c_114, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2])).
% 1.63/1.17  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_114])).
% 1.63/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  Inference rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Ref     : 0
% 1.63/1.17  #Sup     : 22
% 1.63/1.17  #Fact    : 0
% 1.63/1.17  #Define  : 0
% 1.63/1.17  #Split   : 1
% 1.63/1.17  #Chain   : 0
% 1.63/1.17  #Close   : 0
% 1.63/1.17  
% 1.63/1.17  Ordering : KBO
% 1.63/1.17  
% 1.63/1.17  Simplification rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Subsume      : 3
% 1.63/1.17  #Demod        : 11
% 1.63/1.17  #Tautology    : 5
% 1.63/1.17  #SimpNegUnit  : 1
% 1.63/1.17  #BackRed      : 5
% 1.63/1.17  
% 1.63/1.17  #Partial instantiations: 0
% 1.63/1.17  #Strategies tried      : 1
% 1.63/1.17  
% 1.63/1.17  Timing (in seconds)
% 1.63/1.17  ----------------------
% 1.63/1.17  Preprocessing        : 0.27
% 1.63/1.17  Parsing              : 0.15
% 1.63/1.17  CNF conversion       : 0.02
% 1.63/1.17  Main loop            : 0.15
% 1.63/1.17  Inferencing          : 0.05
% 1.63/1.17  Reduction            : 0.04
% 1.63/1.17  Demodulation         : 0.03
% 1.63/1.17  BG Simplification    : 0.01
% 1.63/1.18  Subsumption          : 0.04
% 1.63/1.18  Abstraction          : 0.01
% 1.63/1.18  MUC search           : 0.00
% 1.63/1.18  Cooper               : 0.00
% 1.63/1.18  Total                : 0.44
% 1.63/1.18  Index Insertion      : 0.00
% 1.63/1.18  Index Deletion       : 0.00
% 1.63/1.18  Index Matching       : 0.00
% 1.63/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
