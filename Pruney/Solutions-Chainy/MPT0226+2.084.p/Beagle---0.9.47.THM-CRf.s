%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
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

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(k1_tarski(A_5),k1_tarski(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_15,A_16] :
      ( B_15 = A_16
      | k4_xboole_0(k1_tarski(A_16),k1_tarski(B_15)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_8])).

tff(c_32,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_36,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  
% 1.63/1.15  tff(f_43, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.63/1.15  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.63/1.15  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.63/1.15  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.15  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.15  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(k1_tarski(A_5), k1_tarski(B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.63/1.15  tff(c_29, plain, (![B_15, A_16]: (B_15=A_16 | k4_xboole_0(k1_tarski(A_16), k1_tarski(B_15))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_8])).
% 1.63/1.15  tff(c_32, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.63/1.15  tff(c_36, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_32])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 5
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 0
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 0
% 1.63/1.15  #Demod        : 0
% 1.63/1.15  #Tautology    : 3
% 1.63/1.15  #SimpNegUnit  : 1
% 1.63/1.15  #BackRed      : 0
% 1.63/1.15  
% 1.63/1.15  #Partial instantiations: 0
% 1.63/1.15  #Strategies tried      : 1
% 1.63/1.15  
% 1.63/1.15  Timing (in seconds)
% 1.63/1.15  ----------------------
% 1.63/1.15  Preprocessing        : 0.28
% 1.63/1.16  Parsing              : 0.15
% 1.63/1.16  CNF conversion       : 0.02
% 1.63/1.16  Main loop            : 0.07
% 1.63/1.16  Inferencing          : 0.03
% 1.63/1.16  Reduction            : 0.02
% 1.63/1.16  Demodulation         : 0.01
% 1.63/1.16  BG Simplification    : 0.01
% 1.63/1.16  Subsumption          : 0.01
% 1.63/1.16  Abstraction          : 0.00
% 1.63/1.16  MUC search           : 0.00
% 1.63/1.16  Cooper               : 0.00
% 1.63/1.16  Total                : 0.37
% 1.63/1.16  Index Insertion      : 0.00
% 1.63/1.16  Index Deletion       : 0.00
% 1.63/1.16  Index Matching       : 0.00
% 1.63/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
