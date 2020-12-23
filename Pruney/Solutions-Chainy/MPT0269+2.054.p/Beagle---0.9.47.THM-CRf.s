%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [B_13,A_14] :
      ( k1_tarski(B_13) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [B_15,A_16] :
      ( k1_tarski(B_15) = A_16
      | k1_xboole_0 = A_16
      | k4_xboole_0(A_16,k1_tarski(B_15)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_76,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_67])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  %$ r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  
% 1.63/1.17  tff(f_45, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.63/1.17  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.63/1.17  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.63/1.17  tff(c_14, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.17  tff(c_12, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.17  tff(c_16, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.17  tff(c_51, plain, (![B_13, A_14]: (k1_tarski(B_13)=A_14 | k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.17  tff(c_67, plain, (![B_15, A_16]: (k1_tarski(B_15)=A_16 | k1_xboole_0=A_16 | k4_xboole_0(A_16, k1_tarski(B_15))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.63/1.17  tff(c_76, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_16, c_67])).
% 1.63/1.17  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_76])).
% 1.63/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  Inference rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Ref     : 0
% 1.63/1.17  #Sup     : 15
% 1.63/1.17  #Fact    : 0
% 1.63/1.17  #Define  : 0
% 1.63/1.17  #Split   : 0
% 1.63/1.17  #Chain   : 0
% 1.63/1.17  #Close   : 0
% 1.63/1.17  
% 1.63/1.17  Ordering : KBO
% 1.63/1.17  
% 1.63/1.17  Simplification rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Subsume      : 0
% 1.63/1.17  #Demod        : 0
% 1.63/1.17  #Tautology    : 11
% 1.63/1.17  #SimpNegUnit  : 1
% 1.63/1.17  #BackRed      : 0
% 1.63/1.17  
% 1.63/1.17  #Partial instantiations: 0
% 1.63/1.17  #Strategies tried      : 1
% 1.63/1.17  
% 1.63/1.17  Timing (in seconds)
% 1.63/1.17  ----------------------
% 1.63/1.17  Preprocessing        : 0.29
% 1.63/1.17  Parsing              : 0.15
% 1.63/1.17  CNF conversion       : 0.02
% 1.63/1.17  Main loop            : 0.09
% 1.63/1.17  Inferencing          : 0.04
% 1.63/1.17  Reduction            : 0.03
% 1.63/1.17  Demodulation         : 0.02
% 1.63/1.17  BG Simplification    : 0.01
% 1.63/1.17  Subsumption          : 0.01
% 1.63/1.17  Abstraction          : 0.00
% 1.63/1.17  MUC search           : 0.00
% 1.63/1.17  Cooper               : 0.00
% 1.63/1.17  Total                : 0.40
% 1.63/1.17  Index Insertion      : 0.00
% 1.63/1.17  Index Deletion       : 0.00
% 1.63/1.17  Index Matching       : 0.00
% 1.63/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
