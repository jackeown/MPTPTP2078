%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_17,A_18] :
      ( B_17 = A_18
      | ~ r1_tarski(k1_tarski(A_18),k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | k4_xboole_0(k1_tarski(A_22),k1_tarski(B_21)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_62,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:35:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.19  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.19  
% 1.72/1.19  %Foreground sorts:
% 1.72/1.19  
% 1.72/1.19  
% 1.72/1.19  %Background operators:
% 1.72/1.19  
% 1.72/1.19  
% 1.72/1.19  %Foreground operators:
% 1.72/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.72/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.19  
% 1.72/1.20  tff(f_44, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.72/1.20  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.72/1.20  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.72/1.20  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.20  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.20  tff(c_45, plain, (![B_17, A_18]: (B_17=A_18 | ~r1_tarski(k1_tarski(A_18), k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.20  tff(c_59, plain, (![B_21, A_22]: (B_21=A_22 | k4_xboole_0(k1_tarski(A_22), k1_tarski(B_21))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.72/1.20  tff(c_62, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_16, c_59])).
% 1.72/1.20  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_62])).
% 1.72/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.20  
% 1.72/1.20  Inference rules
% 1.72/1.20  ----------------------
% 1.72/1.20  #Ref     : 0
% 1.72/1.20  #Sup     : 11
% 1.72/1.20  #Fact    : 0
% 1.72/1.20  #Define  : 0
% 1.72/1.20  #Split   : 0
% 1.72/1.20  #Chain   : 0
% 1.72/1.20  #Close   : 0
% 1.72/1.20  
% 1.72/1.20  Ordering : KBO
% 1.72/1.20  
% 1.72/1.20  Simplification rules
% 1.72/1.20  ----------------------
% 1.72/1.20  #Subsume      : 0
% 1.72/1.20  #Demod        : 0
% 1.72/1.20  #Tautology    : 9
% 1.72/1.20  #SimpNegUnit  : 1
% 1.72/1.20  #BackRed      : 0
% 1.72/1.20  
% 1.72/1.20  #Partial instantiations: 0
% 1.72/1.20  #Strategies tried      : 1
% 1.72/1.20  
% 1.72/1.20  Timing (in seconds)
% 1.72/1.20  ----------------------
% 1.72/1.20  Preprocessing        : 0.30
% 1.72/1.20  Parsing              : 0.16
% 1.72/1.20  CNF conversion       : 0.02
% 1.72/1.20  Main loop            : 0.08
% 1.72/1.20  Inferencing          : 0.03
% 1.72/1.20  Reduction            : 0.02
% 1.72/1.20  Demodulation         : 0.01
% 1.72/1.20  BG Simplification    : 0.01
% 1.72/1.20  Subsumption          : 0.01
% 1.72/1.20  Abstraction          : 0.00
% 1.72/1.20  MUC search           : 0.00
% 1.72/1.20  Cooper               : 0.00
% 1.72/1.20  Total                : 0.39
% 1.72/1.20  Index Insertion      : 0.00
% 1.72/1.20  Index Deletion       : 0.00
% 1.72/1.20  Index Matching       : 0.00
% 1.72/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
