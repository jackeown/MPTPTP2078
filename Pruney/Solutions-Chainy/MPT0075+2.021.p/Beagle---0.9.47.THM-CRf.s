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
% DateTime   : Thu Dec  3 09:43:32 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [A_10,C_11,B_12] :
      ( r1_xboole_0(A_10,C_11)
      | ~ r1_xboole_0(B_12,C_11)
      | ~ r1_tarski(A_10,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [A_14] :
      ( r1_xboole_0(A_14,'#skF_2')
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_37])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_86,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_2',A_16)
      | ~ r1_tarski(A_16,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_161,plain,(
    ! [A_28,A_29] :
      ( r1_xboole_0(A_28,A_29)
      | ~ r1_tarski(A_28,'#skF_2')
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_173,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,'#skF_2')
      | ~ r1_tarski(A_30,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_173])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_176])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_202,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_2])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.20  
% 1.90/1.21  tff(f_59, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.90/1.21  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.90/1.21  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.90/1.21  tff(f_48, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.90/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.21  tff(c_18, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_37, plain, (![A_10, C_11, B_12]: (r1_xboole_0(A_10, C_11) | ~r1_xboole_0(B_12, C_11) | ~r1_tarski(A_10, B_12))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.21  tff(c_60, plain, (![A_14]: (r1_xboole_0(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_37])).
% 1.90/1.21  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.90/1.21  tff(c_86, plain, (![A_16]: (r1_xboole_0('#skF_2', A_16) | ~r1_tarski(A_16, '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_4])).
% 1.90/1.21  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.21  tff(c_161, plain, (![A_28, A_29]: (r1_xboole_0(A_28, A_29) | ~r1_tarski(A_28, '#skF_2') | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_86, c_6])).
% 1.90/1.21  tff(c_10, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.90/1.21  tff(c_173, plain, (![A_30]: (k1_xboole_0=A_30 | ~r1_tarski(A_30, '#skF_2') | ~r1_tarski(A_30, '#skF_1'))), inference(resolution, [status(thm)], [c_161, c_10])).
% 1.90/1.21  tff(c_176, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_173])).
% 1.90/1.21  tff(c_179, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_176])).
% 1.90/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.90/1.21  tff(c_202, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_2])).
% 1.90/1.21  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_202])).
% 1.90/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  Inference rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Ref     : 0
% 1.90/1.21  #Sup     : 41
% 1.90/1.21  #Fact    : 0
% 1.90/1.21  #Define  : 0
% 1.90/1.21  #Split   : 6
% 1.90/1.21  #Chain   : 0
% 1.90/1.21  #Close   : 0
% 1.90/1.21  
% 1.90/1.21  Ordering : KBO
% 1.90/1.21  
% 1.90/1.21  Simplification rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Subsume      : 10
% 1.90/1.21  #Demod        : 20
% 1.90/1.21  #Tautology    : 5
% 1.90/1.21  #SimpNegUnit  : 1
% 1.90/1.21  #BackRed      : 11
% 1.90/1.21  
% 1.90/1.21  #Partial instantiations: 0
% 1.90/1.21  #Strategies tried      : 1
% 1.90/1.21  
% 1.90/1.21  Timing (in seconds)
% 1.90/1.21  ----------------------
% 1.90/1.22  Preprocessing        : 0.26
% 1.90/1.22  Parsing              : 0.14
% 1.90/1.22  CNF conversion       : 0.01
% 1.90/1.22  Main loop            : 0.21
% 1.90/1.22  Inferencing          : 0.07
% 1.90/1.22  Reduction            : 0.05
% 1.90/1.22  Demodulation         : 0.04
% 1.90/1.22  BG Simplification    : 0.01
% 1.90/1.22  Subsumption          : 0.06
% 1.90/1.22  Abstraction          : 0.01
% 1.90/1.22  MUC search           : 0.00
% 1.90/1.22  Cooper               : 0.00
% 1.90/1.22  Total                : 0.49
% 1.90/1.22  Index Insertion      : 0.00
% 1.90/1.22  Index Deletion       : 0.00
% 1.90/1.22  Index Matching       : 0.00
% 1.90/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
