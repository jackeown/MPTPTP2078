%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_8,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_21,plain,(
    ! [A_7,C_8,B_9,D_10] :
      ( r1_xboole_0(A_7,C_8)
      | ~ r1_xboole_0(B_9,D_10)
      | ~ r1_tarski(C_8,D_10)
      | ~ r1_tarski(A_7,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_11,C_12] :
      ( r1_xboole_0(A_11,C_12)
      | ~ r1_tarski(C_12,'#skF_3')
      | ~ r1_tarski(A_11,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_21])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [C_13] :
      ( k1_xboole_0 = C_13
      | ~ r1_tarski(C_13,'#skF_3')
      | ~ r1_tarski(C_13,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_6])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_37])).

tff(c_43,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_45,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  
% 1.66/1.15  tff(f_54, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.66/1.15  tff(f_33, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.66/1.15  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.66/1.15  tff(c_8, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.15  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.15  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.15  tff(c_10, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.15  tff(c_21, plain, (![A_7, C_8, B_9, D_10]: (r1_xboole_0(A_7, C_8) | ~r1_xboole_0(B_9, D_10) | ~r1_tarski(C_8, D_10) | ~r1_tarski(A_7, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.16  tff(c_28, plain, (![A_11, C_12]: (r1_xboole_0(A_11, C_12) | ~r1_tarski(C_12, '#skF_3') | ~r1_tarski(A_11, '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_21])).
% 1.66/1.16  tff(c_6, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.16  tff(c_37, plain, (![C_13]: (k1_xboole_0=C_13 | ~r1_tarski(C_13, '#skF_3') | ~r1_tarski(C_13, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_6])).
% 1.66/1.16  tff(c_40, plain, (k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_37])).
% 1.66/1.16  tff(c_43, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 1.66/1.16  tff(c_45, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_43])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 6
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 0
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 0
% 1.66/1.16  #Demod        : 1
% 1.66/1.16  #Tautology    : 1
% 1.66/1.16  #SimpNegUnit  : 1
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.71/1.16  Preprocessing        : 0.28
% 1.71/1.16  Parsing              : 0.15
% 1.71/1.16  CNF conversion       : 0.02
% 1.71/1.16  Main loop            : 0.08
% 1.71/1.16  Inferencing          : 0.03
% 1.71/1.16  Reduction            : 0.02
% 1.71/1.16  Demodulation         : 0.02
% 1.71/1.16  BG Simplification    : 0.01
% 1.71/1.16  Subsumption          : 0.01
% 1.71/1.16  Abstraction          : 0.00
% 1.71/1.16  MUC search           : 0.00
% 1.71/1.16  Cooper               : 0.00
% 1.71/1.16  Total                : 0.37
% 1.71/1.16  Index Insertion      : 0.00
% 1.71/1.16  Index Deletion       : 0.00
% 1.71/1.16  Index Matching       : 0.00
% 1.71/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
