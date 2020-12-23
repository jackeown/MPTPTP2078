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
% DateTime   : Thu Dec  3 09:53:06 EST 2020

% Result     : Theorem 9.97s
% Output     : CNFRefutation 9.97s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_597,plain,(
    ! [A_49,C_50,B_51] :
      ( k1_tarski(A_49) = C_50
      | k1_xboole_0 = C_50
      | k2_xboole_0(B_51,C_50) != k1_tarski(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_609,plain,(
    ! [A_15,B_16,A_49] :
      ( k4_xboole_0(A_15,B_16) = k1_tarski(A_49)
      | k4_xboole_0(A_15,B_16) = k1_xboole_0
      | k1_tarski(A_49) != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_597])).

tff(c_30196,plain,(
    ! [A_336,B_337] :
      ( k4_xboole_0(k1_tarski(A_336),B_337) = k1_tarski(A_336)
      | k4_xboole_0(k1_tarski(A_336),B_337) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_609])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30402,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30196,c_36])).

tff(c_30532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.97/4.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/4.09  
% 9.97/4.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/4.09  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.97/4.09  
% 9.97/4.09  %Foreground sorts:
% 9.97/4.09  
% 9.97/4.09  
% 9.97/4.09  %Background operators:
% 9.97/4.09  
% 9.97/4.09  
% 9.97/4.09  %Foreground operators:
% 9.97/4.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.97/4.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.97/4.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.97/4.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.97/4.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.97/4.09  tff('#skF_2', type, '#skF_2': $i).
% 9.97/4.09  tff('#skF_1', type, '#skF_1': $i).
% 9.97/4.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.97/4.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.97/4.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.97/4.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.97/4.09  
% 9.97/4.09  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 9.97/4.09  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.97/4.09  tff(f_61, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 9.97/4.09  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.97/4.09  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.97/4.09  tff(c_597, plain, (![A_49, C_50, B_51]: (k1_tarski(A_49)=C_50 | k1_xboole_0=C_50 | k2_xboole_0(B_51, C_50)!=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.97/4.09  tff(c_609, plain, (![A_15, B_16, A_49]: (k4_xboole_0(A_15, B_16)=k1_tarski(A_49) | k4_xboole_0(A_15, B_16)=k1_xboole_0 | k1_tarski(A_49)!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_16, c_597])).
% 9.97/4.09  tff(c_30196, plain, (![A_336, B_337]: (k4_xboole_0(k1_tarski(A_336), B_337)=k1_tarski(A_336) | k4_xboole_0(k1_tarski(A_336), B_337)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_609])).
% 9.97/4.09  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.97/4.09  tff(c_30402, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30196, c_36])).
% 9.97/4.09  tff(c_30532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30402])).
% 9.97/4.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/4.10  
% 9.97/4.10  Inference rules
% 9.97/4.10  ----------------------
% 9.97/4.10  #Ref     : 3
% 9.97/4.10  #Sup     : 7593
% 9.97/4.10  #Fact    : 1
% 9.97/4.10  #Define  : 0
% 9.97/4.10  #Split   : 0
% 9.97/4.10  #Chain   : 0
% 9.97/4.10  #Close   : 0
% 9.97/4.10  
% 9.97/4.10  Ordering : KBO
% 9.97/4.10  
% 9.97/4.10  Simplification rules
% 9.97/4.10  ----------------------
% 9.97/4.10  #Subsume      : 76
% 9.97/4.10  #Demod        : 8456
% 9.97/4.10  #Tautology    : 5648
% 9.97/4.10  #SimpNegUnit  : 1
% 9.97/4.10  #BackRed      : 3
% 9.97/4.10  
% 9.97/4.10  #Partial instantiations: 0
% 9.97/4.10  #Strategies tried      : 1
% 9.97/4.10  
% 9.97/4.10  Timing (in seconds)
% 9.97/4.10  ----------------------
% 9.97/4.10  Preprocessing        : 0.30
% 9.97/4.10  Parsing              : 0.16
% 9.97/4.10  CNF conversion       : 0.02
% 9.97/4.10  Main loop            : 3.03
% 9.97/4.10  Inferencing          : 0.66
% 9.97/4.10  Reduction            : 1.74
% 9.97/4.10  Demodulation         : 1.56
% 9.97/4.10  BG Simplification    : 0.08
% 9.97/4.10  Subsumption          : 0.43
% 9.97/4.10  Abstraction          : 0.15
% 9.97/4.10  MUC search           : 0.00
% 9.97/4.10  Cooper               : 0.00
% 9.97/4.10  Total                : 3.35
% 9.97/4.10  Index Insertion      : 0.00
% 9.97/4.10  Index Deletion       : 0.00
% 9.97/4.10  Index Matching       : 0.00
% 9.97/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
