%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k1_tarski(A_10)
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_tarski(A_5,B_6),k1_tarski(B_6)) = k4_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_18,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_115,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:57:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.12  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.66/1.12  
% 1.66/1.12  %Foreground sorts:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Background operators:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Foreground operators:
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.12  
% 1.66/1.13  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.66/1.13  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.66/1.13  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.66/1.13  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.66/1.13  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.13  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k1_tarski(A_10) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.13  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.13  tff(c_53, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.13  tff(c_68, plain, (![A_5, B_6]: (k4_xboole_0(k2_tarski(A_5, B_6), k1_tarski(B_6))=k4_xboole_0(k1_tarski(A_5), k1_tarski(B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_53])).
% 1.66/1.13  tff(c_18, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.13  tff(c_93, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18])).
% 1.66/1.13  tff(c_115, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14, c_93])).
% 1.66/1.13  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_115])).
% 1.66/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  Inference rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Ref     : 1
% 1.66/1.13  #Sup     : 21
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 0
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 2
% 1.66/1.13  #Tautology    : 14
% 1.66/1.13  #SimpNegUnit  : 1
% 1.66/1.13  #BackRed      : 1
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.13  Preprocessing        : 0.28
% 1.66/1.13  Parsing              : 0.15
% 1.66/1.13  CNF conversion       : 0.01
% 1.66/1.13  Main loop            : 0.10
% 1.66/1.13  Inferencing          : 0.04
% 1.66/1.13  Reduction            : 0.03
% 1.66/1.13  Demodulation         : 0.02
% 1.66/1.13  BG Simplification    : 0.01
% 1.66/1.13  Subsumption          : 0.02
% 1.66/1.13  Abstraction          : 0.01
% 1.66/1.13  MUC search           : 0.00
% 1.66/1.13  Cooper               : 0.00
% 1.66/1.13  Total                : 0.41
% 1.66/1.13  Index Insertion      : 0.00
% 1.66/1.13  Index Deletion       : 0.00
% 1.66/1.13  Index Matching       : 0.00
% 1.66/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
