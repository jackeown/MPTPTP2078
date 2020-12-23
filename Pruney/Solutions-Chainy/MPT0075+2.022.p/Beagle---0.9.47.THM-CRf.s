%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:32 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  38 expanded)
%              Number of equality atoms :    5 (   5 expanded)
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

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_12,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13,plain,(
    ! [A_4,B_5,C_6] :
      ( k1_xboole_0 = A_4
      | ~ r1_xboole_0(B_5,C_6)
      | ~ r1_tarski(A_4,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,'#skF_2')
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_13])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_17])).

tff(c_23,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_2])).

tff(c_28,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.35  
% 1.85/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.36  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.36  
% 1.85/1.36  %Foreground sorts:
% 1.85/1.36  
% 1.85/1.36  
% 1.85/1.36  %Background operators:
% 1.85/1.36  
% 1.85/1.36  
% 1.85/1.36  %Foreground operators:
% 1.85/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.36  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.36  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.36  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.36  
% 1.85/1.37  tff(f_45, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.85/1.37  tff(f_34, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.85/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.37  tff(c_12, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.37  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.37  tff(c_8, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.37  tff(c_6, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.37  tff(c_13, plain, (![A_4, B_5, C_6]: (k1_xboole_0=A_4 | ~r1_xboole_0(B_5, C_6) | ~r1_tarski(A_4, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.37  tff(c_17, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, '#skF_2') | ~r1_tarski(A_7, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_13])).
% 1.85/1.37  tff(c_20, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_8, c_17])).
% 1.85/1.37  tff(c_23, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.85/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.85/1.37  tff(c_26, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23, c_2])).
% 1.85/1.37  tff(c_28, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_26])).
% 1.85/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.37  
% 1.85/1.37  Inference rules
% 1.85/1.37  ----------------------
% 1.85/1.37  #Ref     : 0
% 1.85/1.37  #Sup     : 2
% 1.85/1.37  #Fact    : 0
% 1.85/1.37  #Define  : 0
% 1.85/1.37  #Split   : 0
% 1.85/1.37  #Chain   : 0
% 1.85/1.37  #Close   : 0
% 1.85/1.37  
% 1.85/1.37  Ordering : KBO
% 1.85/1.37  
% 1.85/1.37  Simplification rules
% 1.85/1.37  ----------------------
% 1.85/1.37  #Subsume      : 0
% 1.85/1.37  #Demod        : 4
% 1.85/1.37  #Tautology    : 0
% 1.85/1.37  #SimpNegUnit  : 1
% 1.85/1.37  #BackRed      : 3
% 1.85/1.37  
% 1.85/1.37  #Partial instantiations: 0
% 1.85/1.37  #Strategies tried      : 1
% 1.85/1.37  
% 1.85/1.37  Timing (in seconds)
% 1.85/1.37  ----------------------
% 1.85/1.37  Preprocessing        : 0.37
% 1.85/1.37  Parsing              : 0.20
% 1.85/1.37  CNF conversion       : 0.02
% 1.85/1.37  Main loop            : 0.11
% 1.85/1.37  Inferencing          : 0.05
% 1.85/1.37  Reduction            : 0.03
% 1.85/1.37  Demodulation         : 0.02
% 1.85/1.37  BG Simplification    : 0.02
% 1.85/1.37  Subsumption          : 0.01
% 1.85/1.37  Abstraction          : 0.00
% 1.85/1.37  MUC search           : 0.00
% 1.85/1.37  Cooper               : 0.00
% 1.85/1.37  Total                : 0.52
% 1.85/1.37  Index Insertion      : 0.00
% 1.85/1.37  Index Deletion       : 0.00
% 1.85/1.37  Index Matching       : 0.00
% 1.85/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
