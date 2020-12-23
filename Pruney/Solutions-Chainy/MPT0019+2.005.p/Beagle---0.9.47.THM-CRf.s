%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:31 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 124 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    k2_xboole_0('#skF_4','#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_512,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden('#skF_2'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_2'(A_99,B_100,C_101),A_99)
      | r2_hidden('#skF_3'(A_99,B_100,C_101),C_101)
      | k2_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_572,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_2'(A_99,B_100,B_100),A_99)
      | r2_hidden('#skF_3'(A_99,B_100,B_100),B_100)
      | k2_xboole_0(A_99,B_100) = B_100 ) ),
    inference(resolution,[status(thm)],[c_512,c_22])).

tff(c_362,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | r2_hidden('#skF_2'(A_81,B_82,C_83),A_81)
      | ~ r2_hidden('#skF_3'(A_81,B_82,C_83),B_82)
      | k2_xboole_0(A_81,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3713,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_2'(A_306,B_307,B_307),A_306)
      | ~ r2_hidden('#skF_3'(A_306,B_307,B_307),B_307)
      | k2_xboole_0(A_306,B_307) = B_307 ) ),
    inference(resolution,[status(thm)],[c_362,c_14])).

tff(c_3776,plain,(
    ! [A_308,B_309] :
      ( r2_hidden('#skF_2'(A_308,B_309,B_309),A_308)
      | k2_xboole_0(A_308,B_309) = B_309 ) ),
    inference(resolution,[status(thm)],[c_572,c_3713])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3843,plain,(
    ! [A_310,B_311,B_312] :
      ( r2_hidden('#skF_2'(A_310,B_311,B_311),B_312)
      | ~ r1_tarski(A_310,B_312)
      | k2_xboole_0(A_310,B_311) = B_311 ) ),
    inference(resolution,[status(thm)],[c_3776,c_2])).

tff(c_3902,plain,(
    ! [A_310,B_312] :
      ( r2_hidden('#skF_3'(A_310,B_312,B_312),B_312)
      | ~ r1_tarski(A_310,B_312)
      | k2_xboole_0(A_310,B_312) = B_312 ) ),
    inference(resolution,[status(thm)],[c_3843,c_22])).

tff(c_4034,plain,(
    ! [A_320,B_321] :
      ( ~ r2_hidden('#skF_3'(A_320,B_321,B_321),B_321)
      | ~ r1_tarski(A_320,B_321)
      | k2_xboole_0(A_320,B_321) = B_321 ) ),
    inference(resolution,[status(thm)],[c_3843,c_14])).

tff(c_4115,plain,(
    ! [A_322,B_323] :
      ( ~ r1_tarski(A_322,B_323)
      | k2_xboole_0(A_322,B_323) = B_323 ) ),
    inference(resolution,[status(thm)],[c_3902,c_4034])).

tff(c_4172,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_4115])).

tff(c_4195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:06:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.61  
% 6.90/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.61  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.19/2.61  
% 7.19/2.61  %Foreground sorts:
% 7.19/2.61  
% 7.19/2.61  
% 7.19/2.61  %Background operators:
% 7.19/2.61  
% 7.19/2.61  
% 7.19/2.61  %Foreground operators:
% 7.19/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.19/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.19/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.19/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.19/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.19/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.19/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.19/2.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.19/2.61  
% 7.19/2.62  tff(f_46, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.19/2.62  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.19/2.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.19/2.62  tff(c_26, plain, (k2_xboole_0('#skF_4', '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.19/2.62  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.19/2.62  tff(c_512, plain, (![A_99, B_100, C_101]: (r2_hidden('#skF_2'(A_99, B_100, C_101), B_100) | r2_hidden('#skF_2'(A_99, B_100, C_101), A_99) | r2_hidden('#skF_3'(A_99, B_100, C_101), C_101) | k2_xboole_0(A_99, B_100)=C_101)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.19/2.62  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.19/2.62  tff(c_572, plain, (![A_99, B_100]: (r2_hidden('#skF_2'(A_99, B_100, B_100), A_99) | r2_hidden('#skF_3'(A_99, B_100, B_100), B_100) | k2_xboole_0(A_99, B_100)=B_100)), inference(resolution, [status(thm)], [c_512, c_22])).
% 7.19/2.62  tff(c_362, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_2'(A_81, B_82, C_83), B_82) | r2_hidden('#skF_2'(A_81, B_82, C_83), A_81) | ~r2_hidden('#skF_3'(A_81, B_82, C_83), B_82) | k2_xboole_0(A_81, B_82)=C_83)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.19/2.62  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.19/2.62  tff(c_3713, plain, (![A_306, B_307]: (r2_hidden('#skF_2'(A_306, B_307, B_307), A_306) | ~r2_hidden('#skF_3'(A_306, B_307, B_307), B_307) | k2_xboole_0(A_306, B_307)=B_307)), inference(resolution, [status(thm)], [c_362, c_14])).
% 7.19/2.62  tff(c_3776, plain, (![A_308, B_309]: (r2_hidden('#skF_2'(A_308, B_309, B_309), A_308) | k2_xboole_0(A_308, B_309)=B_309)), inference(resolution, [status(thm)], [c_572, c_3713])).
% 7.19/2.62  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.19/2.62  tff(c_3843, plain, (![A_310, B_311, B_312]: (r2_hidden('#skF_2'(A_310, B_311, B_311), B_312) | ~r1_tarski(A_310, B_312) | k2_xboole_0(A_310, B_311)=B_311)), inference(resolution, [status(thm)], [c_3776, c_2])).
% 7.19/2.62  tff(c_3902, plain, (![A_310, B_312]: (r2_hidden('#skF_3'(A_310, B_312, B_312), B_312) | ~r1_tarski(A_310, B_312) | k2_xboole_0(A_310, B_312)=B_312)), inference(resolution, [status(thm)], [c_3843, c_22])).
% 7.19/2.62  tff(c_4034, plain, (![A_320, B_321]: (~r2_hidden('#skF_3'(A_320, B_321, B_321), B_321) | ~r1_tarski(A_320, B_321) | k2_xboole_0(A_320, B_321)=B_321)), inference(resolution, [status(thm)], [c_3843, c_14])).
% 7.19/2.62  tff(c_4115, plain, (![A_322, B_323]: (~r1_tarski(A_322, B_323) | k2_xboole_0(A_322, B_323)=B_323)), inference(resolution, [status(thm)], [c_3902, c_4034])).
% 7.19/2.62  tff(c_4172, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_4115])).
% 7.19/2.62  tff(c_4195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4172])).
% 7.19/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.62  
% 7.19/2.62  Inference rules
% 7.19/2.62  ----------------------
% 7.19/2.62  #Ref     : 0
% 7.19/2.62  #Sup     : 1127
% 7.19/2.62  #Fact    : 6
% 7.19/2.62  #Define  : 0
% 7.19/2.62  #Split   : 0
% 7.19/2.62  #Chain   : 0
% 7.19/2.62  #Close   : 0
% 7.19/2.62  
% 7.19/2.62  Ordering : KBO
% 7.19/2.62  
% 7.19/2.62  Simplification rules
% 7.19/2.62  ----------------------
% 7.19/2.62  #Subsume      : 129
% 7.19/2.62  #Demod        : 22
% 7.19/2.62  #Tautology    : 33
% 7.19/2.62  #SimpNegUnit  : 1
% 7.19/2.62  #BackRed      : 0
% 7.19/2.62  
% 7.19/2.62  #Partial instantiations: 0
% 7.19/2.62  #Strategies tried      : 1
% 7.19/2.62  
% 7.19/2.62  Timing (in seconds)
% 7.19/2.62  ----------------------
% 7.19/2.62  Preprocessing        : 0.44
% 7.19/2.62  Parsing              : 0.22
% 7.19/2.62  CNF conversion       : 0.03
% 7.19/2.62  Main loop            : 1.40
% 7.19/2.62  Inferencing          : 0.37
% 7.19/2.62  Reduction            : 0.24
% 7.19/2.63  Demodulation         : 0.16
% 7.19/2.63  BG Simplification    : 0.06
% 7.19/2.63  Subsumption          : 0.64
% 7.19/2.63  Abstraction          : 0.07
% 7.19/2.63  MUC search           : 0.00
% 7.19/2.63  Cooper               : 0.00
% 7.19/2.63  Total                : 1.87
% 7.19/2.63  Index Insertion      : 0.00
% 7.19/2.63  Index Deletion       : 0.00
% 7.19/2.63  Index Matching       : 0.00
% 7.19/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
