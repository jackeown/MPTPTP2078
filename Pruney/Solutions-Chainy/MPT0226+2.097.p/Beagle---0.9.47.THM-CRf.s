%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:50 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [B_17,A_18] :
      ( B_17 = A_18
      | k4_xboole_0(k1_tarski(A_18),k1_tarski(B_17)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_33,c_12])).

tff(c_45,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.07  
% 1.59/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.08  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.59/1.08  
% 1.59/1.08  %Foreground sorts:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Background operators:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Foreground operators:
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.08  
% 1.68/1.08  tff(f_52, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.68/1.08  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.68/1.08  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.68/1.08  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.08  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.08  tff(c_33, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.08  tff(c_12, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.08  tff(c_42, plain, (![B_17, A_18]: (B_17=A_18 | k4_xboole_0(k1_tarski(A_18), k1_tarski(B_17))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_12])).
% 1.68/1.08  tff(c_45, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_16, c_42])).
% 1.68/1.08  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_45])).
% 1.68/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  
% 1.68/1.08  Inference rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Ref     : 0
% 1.68/1.08  #Sup     : 7
% 1.68/1.08  #Fact    : 0
% 1.68/1.08  #Define  : 0
% 1.68/1.08  #Split   : 0
% 1.68/1.08  #Chain   : 0
% 1.68/1.08  #Close   : 0
% 1.68/1.08  
% 1.68/1.08  Ordering : KBO
% 1.68/1.08  
% 1.68/1.08  Simplification rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Subsume      : 0
% 1.68/1.08  #Demod        : 0
% 1.68/1.08  #Tautology    : 4
% 1.68/1.08  #SimpNegUnit  : 1
% 1.68/1.08  #BackRed      : 0
% 1.68/1.08  
% 1.68/1.08  #Partial instantiations: 0
% 1.68/1.08  #Strategies tried      : 1
% 1.68/1.08  
% 1.68/1.08  Timing (in seconds)
% 1.68/1.08  ----------------------
% 1.68/1.09  Preprocessing        : 0.26
% 1.68/1.09  Parsing              : 0.14
% 1.68/1.09  CNF conversion       : 0.02
% 1.68/1.09  Main loop            : 0.07
% 1.68/1.09  Inferencing          : 0.03
% 1.68/1.09  Reduction            : 0.02
% 1.68/1.09  Demodulation         : 0.01
% 1.68/1.09  BG Simplification    : 0.01
% 1.68/1.09  Subsumption          : 0.01
% 1.68/1.09  Abstraction          : 0.00
% 1.68/1.09  MUC search           : 0.00
% 1.68/1.09  Cooper               : 0.00
% 1.68/1.09  Total                : 0.36
% 1.68/1.09  Index Insertion      : 0.00
% 1.68/1.09  Index Deletion       : 0.00
% 1.68/1.09  Index Matching       : 0.00
% 1.68/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
