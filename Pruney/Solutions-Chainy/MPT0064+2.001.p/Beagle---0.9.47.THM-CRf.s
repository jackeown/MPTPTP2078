%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:10 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   13 (  14 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_6,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7,plain,(
    ! [B_3,A_4] :
      ( ~ r2_xboole_0(B_3,A_4)
      | ~ r2_xboole_0(A_4,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_9,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_7])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.38/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.38/1.10  
% 1.38/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.10  %$ r2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.47/1.10  
% 1.47/1.10  %Foreground sorts:
% 1.47/1.10  
% 1.47/1.10  
% 1.47/1.10  %Background operators:
% 1.47/1.10  
% 1.47/1.10  
% 1.47/1.10  %Foreground operators:
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.10  
% 1.47/1.11  tff(f_36, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_xboole_1)).
% 1.47/1.11  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.47/1.11  tff(c_6, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.47/1.11  tff(c_4, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.47/1.11  tff(c_7, plain, (![B_3, A_4]: (~r2_xboole_0(B_3, A_4) | ~r2_xboole_0(A_4, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.47/1.11  tff(c_9, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_7])).
% 1.47/1.11  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.47/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.11  
% 1.47/1.11  Inference rules
% 1.47/1.11  ----------------------
% 1.47/1.11  #Ref     : 0
% 1.47/1.11  #Sup     : 2
% 1.47/1.11  #Fact    : 0
% 1.47/1.11  #Define  : 0
% 1.47/1.11  #Split   : 0
% 1.47/1.11  #Chain   : 0
% 1.47/1.11  #Close   : 0
% 1.47/1.11  
% 1.47/1.11  Ordering : KBO
% 1.47/1.11  
% 1.47/1.11  Simplification rules
% 1.47/1.11  ----------------------
% 1.47/1.11  #Subsume      : 0
% 1.47/1.11  #Demod        : 1
% 1.47/1.11  #Tautology    : 0
% 1.47/1.11  #SimpNegUnit  : 0
% 1.47/1.11  #BackRed      : 0
% 1.47/1.11  
% 1.47/1.11  #Partial instantiations: 0
% 1.47/1.11  #Strategies tried      : 1
% 1.47/1.11  
% 1.47/1.11  Timing (in seconds)
% 1.47/1.11  ----------------------
% 1.47/1.11  Preprocessing        : 0.21
% 1.47/1.11  Parsing              : 0.12
% 1.47/1.11  CNF conversion       : 0.01
% 1.47/1.11  Main loop            : 0.05
% 1.47/1.11  Inferencing          : 0.02
% 1.47/1.12  Reduction            : 0.01
% 1.47/1.12  Demodulation         : 0.01
% 1.47/1.12  BG Simplification    : 0.01
% 1.47/1.12  Subsumption          : 0.01
% 1.47/1.12  Abstraction          : 0.00
% 1.47/1.12  MUC search           : 0.00
% 1.47/1.12  Cooper               : 0.00
% 1.47/1.12  Total                : 0.29
% 1.47/1.12  Index Insertion      : 0.00
% 1.47/1.12  Index Deletion       : 0.00
% 1.47/1.12  Index Matching       : 0.00
% 1.47/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
